(* ::Package:: *)

(* ::Section:: *)
(*Style*)


MyColor1=RGBColor[{62,55,51}/256];
MyColor2=RGBColor[{252,67,73}/256];
MyColor3=RGBColor[{59,138,179}/256];
MyColor4=RGBColor[{233,171,88}/256];
MyColor5=RGBColor[{73,160,88}/256];
MyColor6=RGBColor[{160,160,120}/256];
MyColor7=RGBColor[{170,88,180}/256];
MyColor={MyColor1,MyColor2,MyColor3,MyColor4,MyColor5,MyColor6,MyColor7}
MyStyle={{MyColor1,Dashing[{1,0}]},{MyColor2,Dashing[{0.008,0.008,0.04,0.008}]},{MyColor3,Dashing[{0.02,0.004}]},{MyColor4,Dashing[{0.02,0.02}]},{MyColor7,Dashing[{0.04,0.04}]}};
MyStylel={{MyColor1,Dashing[{1,0}],AbsoluteThickness[0.8]},{MyColor2,Dashing[{0.008,0.008,0.04}],AbsoluteThickness[0.8]},
{MyColor3,Dashing[{0.02,0.004}],AbsoluteThickness[0.8]},{MyColor4,Dashing[{0.02,0.02}],AbsoluteThickness[0.8]}};
MyStyleO={{MyColor1,Opacity[0.2]},{MyColor2,Opacity[0.2]},
{MyColor3,Opacity[0.2]},{MyColor4,Opacity[0.2]}};


(* ::Section:: *)
(*Initialize*)


(* ::Subsection:: *)
(*Importing the xAct*)


Block[{Print},<< xAct`xTensor`]; 
Block[{Print},<< xAct`xTras`]; 
Block[{Print}, <<xAct`xCoba`];
Block[{Print}, << xAct`xPert`];
Block[{Print}, << xAct`TexAct`];


(* ::Subsubsection:: *)
(*Display *)


$CovDFormat = "Prefix";


(* ::Subsection:: *)
(*Definition of background*)


(* ::Subsubsection:: *)
(*Manifold*)


M4::usage = "4-Manifolds.";
Index4d={\[Alpha],\[Beta],\[Gamma],\[Delta],\[Sigma],\[Mu],\[Nu]}
DefManifold[M4,4,Index4d]


(* ::Subsubsection:: *)
(*Metric*)


Block[{Print}, DefMetric[-1,gmetric[-\[Alpha],-\[Beta]],CD,PrintAs->"g"]];


(* ::Subsubsection:: *)
(*Proper time*)


DefParameter[tau,PrintAs->"\[Tau]"]


(* ::Subsubsection:: *)
(*Chart*)


(* ::Text:: *)
(**)


B::usage = "4-Chart."


Block[{Print},DefChart[B,M4,{0,1,2,3},{t[], r[], \[Theta][], \[Phi][]},FormatBasis->{"Partials","Differentials"}, ChartColor -> MyColor3]];


(* ::Subsubsection:: *)
(*Perturbation of  \[Theta]*)


DefTensor[\[Delta]\[Theta][],M4]


(* ::Subsubsection:: *)
(*Metric*)


DefScalarFunction[f,PrintAs->"f"];


MatrixForm[TheMetric={{-f[r[]],0,0,0}, {0,1/f[r[]],0,0},{0,0,r[]^2,0},{0,0,0,r[]^2 Sin[\[Theta][]]^2}}];


Block[{Print},MetricInBasis[gmetric,-B,TheMetric]]//MatrixForm;


(* ::Subsubsection:: *)
(*Type of Metric*)


(* ::Subsubsubsection:: *)
(*parameters*)


G::usage = "Gravitational constant G";
M::usage = "Black hole mass M.";
b::usage = "Brane world parameter b.";
DefConstantSymbol[G];
DefConstantSymbol[M];
DefConstantSymbol[b];


(* ::Subsubsubsection:: *)
(*function*)


fSh[r_]:=1- 2/r;


fShBW[r_]:=1- 2/r+ b/r^2;


(* ::Subsubsection:: *)
(*Per-computation of curvature tensors, etc\:ff1a*)


(* ::Subsubsubsection:: *)
(*Per-computation\:ff1a*)


MetricCompute[gmetric,B,All]


(* ::Subsubsubsection:: *)
(*Others*)


Block[{Print}, ChangeComponents[RicciCD[{\[Alpha],B}, {\[Beta],B}],RicciCD[{-\[Alpha],-B}, {-\[Beta],-B}]]];


Block[{Print}, ChangeComponents[RiemannCD[{-\[Alpha],-B}, {-\[Beta],-B},{\[Mu],B}, {-\[Nu],-B}],RiemannCD[{-\[Alpha],-B}, {-\[Beta],-B},{-\[Mu],-B}, {-\[Nu],-B}]]];


Block[{Print}, ChangeComponents[epsilongmetric[{\[Alpha],B}, {\[Beta],B},{-\[Mu],-B}, {-\[Nu],-B}],epsilongmetric[{-\[Alpha],-B}, {-\[Beta],-B},{-\[Mu],-B}, {-\[Nu],-B}]]];


Block[{Print}, ChangeComponents[epsilongmetric[{\[Alpha],B}, {\[Beta],B},{\[Mu],B}, {\[Nu],B}],epsilongmetric[{-\[Alpha],-B}, {-\[Beta],-B},{-\[Mu],-B}, {-\[Nu],-B}]]];


(* ::Subsubsection:: *)
(*Full inverse tensor*)


(* ::Input:: *)
(*MySimplify@Sqrt[-DetgmetricB[]]*)


RuleEg=MakeRule[{epsilongmetric[{0, -B}, {1, -B}, {2, -B}, {3, -B}],MySimplify@Sqrt[-Detgmetric[]]},MetricOn->All];
EgtoUnit[exp_]:=Module[{},exp/.RuleEg];


(* ::Subsubsection:: *)
(*MySimplify*)


(* ::Text:: *)
(*"MySimplify" learn from the  <Calculation of the charges of  Kerr-Newman BH by the solution phase space method > *)


(* ::Text:: *)
(* Kamal Hajian*)
(*Institute for Research in Fundamental Sciences (IPM), School of Physics*)


MySimplify1[a_]:=ChangeCovD[a,CD,PDB];
MySimplify2[b_]:=ToBasis[B]@ToBasis[B]@MySimplify1[b];
MySimplify3[c_]:=TraceBasisDummy@MySimplify2[c];
MySimplify4[d_]:=ComponentArray@MySimplify3[d];
MySimplify5[e_]:=Factor@ToValues@ToValues@ToValues@MySimplify4[e];
MySimplify[f_]:=Simplify[MySimplify5[f],TimeConstraint->1000];


 org[expr_]:= Collect[ContractMetric[expr], $PerturbationParameter, ToCanonical];


(* ::Section:: *)
(*Assumptions*)


$Assumptions=And[t[]\[Element]Reals,r[]\[Element]Reals,r[]>0,\[Theta][]\[Element]Reals,\[Pi]>=\[Theta][]>=0,\[Phi][]\[Element]Reals,G\[Element]Reals,G>0,M\[Element]Reals,M>=0,-1+e^2<0,p>0];


(* ::Section:: *)
(*Parameters of test particle *)


(* ::Subsubsubsection:: *)
(*Mass*)


DefConstantSymbol[m];


(* ::Subsubsubsection:: *)
(*Position, velocity, momentum*)


DefTensor[P[\[Alpha]],M4,PrintAs->"P"];
DefTensor[xp[\[Alpha]],M4,PrintAs->"x"];
DefTensor[dxp[\[Alpha]],M4,PrintAs->"\!\(\*OverscriptBox[\(x\), \(.\)]\)"];


RuleP=MakeRule[{P[\[Alpha]], m dxp[\[Alpha]]},MetricOn->All];
Ptodx[exp_]:=Module[{},exp/.RuleP];


AllComponentValues[dxp[{\[Alpha],B}],{OverDot[t[]], OverDot[r[]], OverDot[\[Theta][]], OverDot[\[Phi][]]}];
Block[{Print}, AllComponentValues[dxp[{-\[Alpha],B}],MySimplify[gmetric[-\[Beta],-\[Alpha]]dxp[\[Alpha]]]]];


(* ::Subsubsubsection:: *)
(*Spin*)


DefTensor[S[\[Alpha],\[Beta]],M4,Antisymmetric[{\[Alpha],\[Beta]}]];
DefTensor[spin[\[Alpha]],M4,PrintAs->"s"];
DefTensor[s[],M4,PrintAs->"\!\(\*
StyleBox[\"s\",\nFontColor->RGBColor[0.25882352941176473`, 0.49019607843137253`, 0.5568627450980392]]\)"];
DefTensor[sE[\[Alpha]],M4,PrintAs->"\!\(\*SubscriptBox[\(s\), \(\[Perpendicular]\)]\)"];


DefConstantSymbol[sn];
DefConstantSymbol[sp];


AllComponentValues[sE[{\[Alpha],B}],{0,0,s[]/r[],0}];
Block[{Print}, AllComponentValues[sE[{-\[Alpha],B}],MySimplify[gmetric[-\[Beta],-\[Alpha]]sE[\[Alpha]]]]];


AllComponentValues[S[{\[Alpha],B},{\[Beta],B}],{{0,S[{0, B}, {1, B}],0,S[{0, B}, {3, B}]},{-S[{0, B}, {1, B}],0,0,S[{1, B}, {3, B}]},{0,0,0,0},{-S[{0, B}, {3, B}],-S[{1, B}, {3, B}],0,0}}];
Block[{Print}, AllComponentValues[S[{-\[Alpha],B},{-\[Beta],B}],MySimplify[gmetric[-\[Mu],-\[Alpha]]gmetric[-\[Nu],-\[Beta]]S[\[Alpha],\[Beta]]]]];


RuleSE=MakeRule[{S[\[Alpha],\[Beta]],epsilongmetric[\[Alpha],\[Beta],-\[Mu],-\[Nu]] P[\[Mu]]sE[\[Nu]]},MetricOn->All];
StosE[exp_]:=Module[{},exp/.RuleSE];


RuleS=MakeRule[{S[\[Alpha],\[Beta]],epsilongmetric[\[Alpha],\[Beta],-\[Mu],-\[Nu]] P[\[Mu]]spin[\[Nu]]},MetricOn->All];
Stos[exp_]:=Module[{},exp/.RuleS];


(* ::Input:: *)
(*{MatrixForm@Simplify@EgtoUnit@MySimplify@StosE@S[\[Alpha],\[Beta]],MatrixForm@Simplify@EgtoUnit@MySimplify@StosE@S[-\[Alpha],-\[Beta]]}/.{\[Theta][]->\[Pi]/2}*)
(*Simplify@MySimplify@Ptodx@(P[\[Alpha]]P[-\[Alpha]])*)
(*Simplify@MySimplify@Ptodx@StosE@(S[\[Alpha],\[Beta]]S[-\[Alpha],-\[Beta]])*)
(*Simplify@MySimplify@Ptodx@StosE@(sE[\[Alpha]]sE[-\[Alpha]])*)


(* ::Subsubsubsection:: *)
(*Conserved quantity*)


DefConstantSymbol[\[ScriptCapitalJ]];
DefConstantSymbol[\[ScriptCapitalE]];


(* ::Section:: *)
(*Special derivative*)


Dd[exp_]:=Module[{\[Alpha]},dxp[\[Alpha]] CD[-\[Alpha]][exp]];


(* ::Section:: *)
(*Definition in Parallel transport*)


DefTensor[Eb[\[Alpha]],M4];


DefTensor[En[\[Alpha]],M4];


DefScalarFunction[\[Psi]r];


DefTensor[\[Psi][],M4];


(* ::Subsection:: *)
(*Marck's tetrad*)


Block[{Print},DefBasis[BMarck,TangentM4,{0,1,2,3},BasisColor -> MyColor5]];


MySimplifyMarck[f_]:=Simplify[Factor@ToValues@ToValues@ToValues@ComponentArray@TraceBasisDummy@ToBasis[BMarck]@ToBasis[BMarck]@ChangeCovD[f,CD,PDBMarck],TimeConstraint->1000];


(* ::Subsection:: *)
(*Orders*)


DefConstantSymbol[\[Epsilon]];


Orders[exp_]:=Module[{},Expand@exp/.{spin[{0, B}]->\[Epsilon] spin[{0, B}],spin[{1, B}]->\[Epsilon] spin[{1, B}],spin[{2, B}]->\[Epsilon] spin[{2, B}],spin[{3, B}]->\[Epsilon] spin[{3, B}],spin[{0, BMarck}]->\[Epsilon] spin[{0, BMarck}],spin[{1, BMarck}]->\[Epsilon] spin[{1, BMarck}],spin[{2, BMarck}]->\[Epsilon] spin[{2, BMarck}],spin[{3, BMarck}]->\[Epsilon] spin[{3, BMarck}]}];


(* ::Section:: *)
(*Kepler parameter*)


rperi::usage = "\!\(\*SubscriptBox[\(r\), \(peri\)]\) (dimensionless) periapsis.";
rapo::usage = "\!\(\*SubscriptBox[\(r\), \(apo\)]\) (dimensionless) apoapsis.";
p::usage = "p(dimensionless) semilatus rectum.";
e::usage = "e(dimensionless) Eccentricity.";


DefConstantSymbol[rperi,PrintAs->"\!\(\*SubscriptBox[\(r\), \(peri\)]\)"];
DefConstantSymbol[rapo,PrintAs->"\!\(\*SubscriptBox[\(r\), \(apo\)]\)"];
DefConstantSymbol[e];
DefConstantSymbol[p];
DefTensor[psi[],M4,PrintAs->"\!\(\*SubscriptBox[\(\[Psi]\), \(r\)]\)"];


(* ::Subsection::Closed:: *)
(*Simplify*)


XYZtoep[exp_]:=Module[{},exp/.{V->(p X-2 b (-2+Z)),W->(p^2 (4 b+Y)-2 b p (2+p) Z+b^2 Z^2)}/.{X->-3-e^2+p,Y->(-2+p)^2-4 e^2, Z->1-e^2}];
eptoXYZ[exp_]:=Module[{},exp/.{3+e^2-p->-X,-3-e^2+p->X}
/.{e^4->(1-Z)^2,e^2->1-Z}
/.{(-2+p)^2->Y+4(1-Z),(-4+p) p->Y-4 Z}
/.{-p X+2 b (-2+Z)->-V,(p X-2 b (-2+Z))->V,2 b (-2+Z)-p (-4+p+Z)->-V}
/.{(p^2 (4 b+Y)-2 b p (2+p) Z+b^2 Z^2)->W}/.{(b (1+e)^2+p (-2-2 e+p)) (b (-1+e)^2+p (-2+2 e+p))->W}
/.{p^2 V-W-p V Z->-(b-p)^2 Z^2,-p^2 V+W+p V Z->(b-p)^2 Z^2}
/.{(b-p) (b^2 p+b (-1+p) p^2-p^3+b^3 (1-Z))->U1,(b-p) (b^2 p+b (-1+p) p^2-p^3-b^3 (-1+Z))->U1,-b^2 p-b (-1+p) p^2+p^3+b^3 (-1+Z)->U1/(p-b)}
/.{(4 b p+(-4+p) p^2-b^2 Z)->(p^2 V-W)/Z}];



(* ::Input:: *)
(*(p^2 V-W)/Z==(4 b p+(-4+p) p^2-b^2 Z)*)
(*(b (1+e)^2+p (-2-2 e+p)) (b (-1+e)^2+p (-2+2 e+p))==(p^2 (4 b+Y)-2 b p (2+p) Z+b^2 Z^2)//XYZtoep//FullSimplify*)


(* ::Input:: *)
(*(b^2 p+b (-1+p) p^2-p^3+b^3 (1-Z))//XYZtoep//FullSimplify*)
(*W//XYZtoep//FullSimplify*)
(*(b-p) (b^2 p+b (-1+p) p^2-p^3+b^3 (1-Z))==(b-p) (b^2 p+b (-1+p) p^2-p^3-b^3 (-1+Z))//Simplify*)


(* ::Subsection:: *)
(*Transform the perihelion and aphelion into the eccentricity and the dimensionless semimajor.*)


rarpTope[exp_]:=Module[{exp0=exp,ReplaceSet},
ReplaceSet={rapo->p/(1-e),rperi-> p/(1+e)}; exp0/.ReplaceSet];
rarpTope0[exp_]:=Module[{exp0=exp,ReplaceSet},
ReplaceSet={rapo-> p,rperi-> p}; exp0/.ReplaceSet];


(* ::Subsection:: *)
(*Coefficient equation*)


K2[r_]:=f[r]/ (r^2);
K3[r_]:= (sp (-2 f[r]+r Derivative[1][f][r]))/r^2;

fEJ02sp[r_]:=Sqrt[\[ScriptCapitalE]20] Sqrt[\[ScriptCapitalJ]20] K3[r];
fJ02sp[r_]:=-K2[r]+(Sqrt[\[ScriptCapitalE]20] K3[r])/(2 Sqrt[\[ScriptCapitalJ]20]);
fE02sp[r_]:=(1+(Sqrt[\[ScriptCapitalJ]20] K3[r])/(2 Sqrt[\[ScriptCapitalE]20]));


(* ::Subsection:: *)
(*ParamExactBW*)


ParamExactBW::usage = "ParamExactBW[sp,sn,e,p,b,M][Exp_] gives a concrete expression for {e,p}.";


ParamExactBW[spE_,snE_,eE_,pE_,bE_,ME_][Exp_]:=Module[{r0,r1E,r2E,r3E,r4E,rnE,rpE,k0E,hrE,hr32E,hrnE,hrpE,
A0f,A1f,A2f,A3f,K1,K2,K3,fEJ02sp,fJ02sp,fE02sp,
\[ScriptCapitalE]2Approxep,\[ScriptCapitalE]20,\[ScriptCapitalJ]2Approxep,\[ScriptCapitalJ]20,\[ScriptCapitalE]E,\[ScriptCapitalJ]E,qr0E,qt0E,q\[CurlyPhi]0E,q\[Psi]0E,
XE,YE,ZE,WE,VE,UE,U1E,U2E,U3E,WsE,WbpE},

XE=pE-3-eE^2;
YE=(pE-2)^2-4 eE^2;
ZE=1-eE^2;
WE=(pE^2 YE+2 bE pE (-2+pE+(2+pE) (1-ZE))+bE^2 ZE^2);
VE=pE XE-2 bE(-2+ZE);
UE=(bE-pE) (bE^2 pE+bE(-1+pE) pE^2-pE^3-bE^3 (-1+ZE));

U1E=(bE-pE) (bE^2 pE+bE (-1+pE) pE^2-pE^3-bE^3 (-1+ZE));
U2E=2 pE^5+bE^2 pE^2 (16-pE (-2+ZE))+2 bE^3 pE (pE (-2+ZE)-3 ZE)+bE^4 ZE^2+2 bE pE^3 (-8-(-2+pE) pE+ZE);
U3E=bE^2 ZE^2-2 bE pE (pE (-2+ZE)+2 ZE)+pE^2 ((-4+pE) pE+4 ZE);

WsE = pE (9-2 pE+3 (1-ZE))-8 bE (2-ZE); 
WbpE = (-bE+pE) WE;

r1E=pE/(1-eE); 
r2E=pE/(1+eE);



\[ScriptCapitalE]2Approxep=(spE ZE^2 Sqrt[-((bE-pE) (pE^2 (4 bE+YE)-2 bE pE (2+pE) ZE+bE^2 ZE^2))] (pE^2+bE (-2 pE+ZE)))/(pE^3 (pE XE-2 bE (-2+ZE))^2)+(pE^2 YE+bE^2 ZE^2-2 bE pE (pE (-2+ZE)+2 ZE))/(pE^2 (pE XE-2 bE (-2+ZE))); 
\[ScriptCapitalJ]2Approxep=(pE^2 (-bE+pE))/(pE XE+2 bE (2-ZE))+(spE (pE (9-2 pE+3 (1-ZE))-8 bE (2-ZE)) Sqrt[(-bE+pE) (pE^2 YE+2 bE pE (-2+pE+(2+pE) (1-ZE))+bE^2 ZE^2)])/(pE XE+2 bE (2-ZE))^2; 


\[ScriptCapitalE]E=Sqrt[\[ScriptCapitalE]2Approxep]; 
\[ScriptCapitalJ]E=Sqrt[\[ScriptCapitalJ]2Approxep]; 

A0f=(bE (4 spE \[ScriptCapitalE]E \[ScriptCapitalJ]E+\[ScriptCapitalJ]E^2))/(1-\[ScriptCapitalE]E^2);
A1f=(2 (3 spE \[ScriptCapitalE]E \[ScriptCapitalJ]E+\[ScriptCapitalJ]E^2))/(-1+\[ScriptCapitalE]E^2); 
A2f=(bE+2 spE \[ScriptCapitalE]E \[ScriptCapitalJ]E+\[ScriptCapitalJ]E^2)/(1-\[ScriptCapitalE]E^2);
A3f=2/(-1+\[ScriptCapitalE]E^2);



r3E=(pE ((bE-pE)^2+Sqrt[(bE-pE) (bE^2 pE+bE (-1+pE) pE^2-pE^3-bE^3 (-1+ZE))]) ZE)/(pE^2 VE-WE)+spE ((pE Sqrt[(-bE+pE) WE] ZE^2 (pE^2+bE (-2 pE+ZE)))/(-pE^2 VE+WE)^2+(Sqrt[(-bE+pE) WE] ZE (2 pE^5+bE^2 pE^2 (16-pE (-2+ZE))+2 bE^3 pE (pE (-2+ZE)-3 ZE)+bE^4 ZE^2+2 bE pE^3 (-8-(-2+pE) pE+ZE)))/(2 (pE^2 VE-WE) Sqrt[-((bE-pE) (-bE^2 pE-bE (-1+pE) pE^2+pE^3+bE^3 (-1+ZE)))] (4 bE pE+(-4+pE) pE^2-bE^2 ZE)));
r4E=-((bE (bE-pE) pE)/((bE-pE)^2+Sqrt[UE]))+(bE spE (-pE^2 VE+WE)^2 (-((2 Sqrt[-bE+pE] ((bE-pE)^2+Sqrt[UE]) (2 (-2+pE) pE+bE ZE) Sqrt[bE^2 ZE^2-2 bE pE (pE (-2+ZE)+2 ZE)+pE^2 ((-4+pE) pE+4 ZE)])/(ZE^2 (-pE (4 bE+(-4+pE) pE)+bE^2 ZE)^3))-(((-bE+pE) WE)^(3/2) ((2 pE^5+bE^2 pE^2 (16-pE (-2+ZE))+2 bE^3 pE (pE (-2+ZE)-3 ZE)-2 bE pE^3 (8-2 pE+pE^2-ZE)+bE^4 ZE^2)/(Sqrt[UE] ZE (4 bE pE+(-4+pE) pE^2-bE^2 ZE)^2)+(2 pE ZE (pE^2+bE (-2 pE+ZE)))/(-pE^2 VE+WE)^2))/((pE^2 VE-WE) WE)))/(2 ((bE-pE)^2+Sqrt[UE])^2);



rnE=1-Sqrt[1-bE]; 
rpE=1+Sqrt[1-bE];  
k0E=Sqrt[(r1E-r2E)/(r1E-r3E) (r3E-r4E)/(r2E-r4E)];  
hrE=(r1E-r2E)/(r1E-r3E); 
hr32E=(r1E-r2E)/(r1E-r3E) r3E/r2E; 
hrnE=(r1E-r2E)/(r1E-r3E) (r3E-rnE)/(r2E-rnE);  
hrpE=(r1E-r2E)/(r1E-r3E) (r3E-rpE)/(r2E-rpE); 

qr0E=0;qt0E=0;q\[CurlyPhi]0E=0;q\[Psi]0E=\[Pi];

Exp/.{f->fShBW}/.{A0->A0f,A1->A1f,A2->A2f,A3->A3f}/.{X->XE,Y->YE,Z->ZE,W->WE,V->VE,U->UE}/.{U1->U1E,U2->U2E,U3->U3E}/.{Ws->WsE,Wbp->WbpE}/.{sn->snE,sp->spE,e->eE,p->pE,b->bE,M->ME}
/.{r1->r1E,r2->r2E,r3->r3E,r4->r4E,rn->rnE,rp->rpE}/.{k0->k0E,hr->hrE,hr32->hr32E,hrp->hrpE,hrn->hrnE}/.{qr0->qr0E,qt0->qt0E,q\[CurlyPhi]0->q\[CurlyPhi]0E,q\[Psi]0->q\[Psi]0E}/.{\[ScriptCapitalE]->\[ScriptCapitalE]E,\[ScriptCapitalJ]->\[ScriptCapitalJ]E}]


(* ::Section::Closed:: *)
(*Conclusion*)


XE=p-3-e^2;
YE=(p-2)^2-4 e^2;
ZE=1-e^2;
WE=(p^2 YE+2 b p (-2+p+(2+p) (1-ZE))+b^2 ZE^2);
VE=p XE-2 b (-2+ZE);
U1E=(b-p) (b^2 p+b (-1+p) p^2-p^3-b^3 (-1+ZE));
U2E=2 p^5+b^2 p^2 (16-p (-2+ZE))+2 b^3 p (p (-2+ZE)-3 ZE)+b^4 ZE^2+2 b p^3 (-8-(-2+p) p+ZE);
U3E=b^2 ZE^2-2 b p (p (-2+ZE)+2 ZE)+p^2 ((-4+p) p+4 ZE);

r1solep=p/(1-e);
r2solep=p/(1+e);
r3solep=(p ((b-p)^2+Sqrt[U1])Z)/(p^2 V-W)+sp Z^2 Sqrt[(-b+p) W]/(2(p^2 V-W)^2) (2 p (p^2+b (-2 p+Z))+ U2/Sqrt[U1]);
r4solep=-((b (b-p) p)/((b-p)^2+Sqrt[U1]))+sp (b Z Sqrt[(-b+p)])/(2 ((b-p)^2+Sqrt[U1])^2 (p^2 V-W)) (2((b-p)^2+Sqrt[U1]) (2 (-2+p) p+b Z) Sqrt[U3]-Sqrt[W](-b+p)(2 p(p^2+b (-2 p+Z))+U2/Sqrt[U1]));


(* ::Subsection:: *)
(*Integral solutions of motion*)


\[Lambda]r0[\[Chi]_]:=(2 EllipticF[\[Chi],k0^2])/(Sqrt[1-\[ScriptCapitalE]^2] Sqrt[(r1-r3) (r2-r4)]);


Tr0[\[Chi]_]:=1/(Sqrt[1-\[ScriptCapitalE]^2] Sqrt[(r1-r3) (r2-r4) ] ) (
((r1-r2) Sqrt[(r1-r3) (r2-r4)] \[ScriptCapitalE] Sin[2 \[Chi]]  Sqrt[-(-((r1-r3) (r2-r4))+(r1-r2) (r3-r4) Sin[\[Chi]]^2)])/(2 r3-(r1+r2)-(r1-r2) Cos[2 \[Chi]])
+(r1-r3) (r2-r4) \[ScriptCapitalE] EllipticE[\[Chi],k0^2]
+1/((r3-rn) (r3-rp)) (-2 (rnIntCharge) (r3-rp)+2 (r3-rn) rpIntCharge+(8-2 b+r1 (-r2+r3)+r3 (4+r2+r3)) (r3-rn) (r3-rp)\[ScriptCapitalE]) EllipticF[\[Chi],k0^2]
+(r2-r3) ((4+r1+r2+r3+r4) \[ScriptCapitalE]) EllipticPi[(r1-r2)/(r1-r3),\[Chi],k0^2]
+(2 (r2-r3) rnIntCharge EllipticPi[((r1-r2) (r3-rn))/((r1-r3) (r2-rn)),\[Chi],k0^2])/((r2-rn) (r3-rn))+(2 (r2-r3) rpIntCharge EllipticPi[((r1-r2) (r3-rp))/((r1-r3) (r2-rp)),\[Chi],k0^2])/((r2-rp) (-r3+rp))
)/.{rpIntCharge->1/(rp-rn) (( +8 \[ScriptCapitalE]-4 b \[ScriptCapitalE]+sp \[ScriptCapitalJ] ) rp+ b( (-4+b)\[ScriptCapitalE]-sp \[ScriptCapitalJ])),rnIntCharge-> 1/(rp-rn) ((  8 \[ScriptCapitalE]-4 b \[ScriptCapitalE]+sp \[ScriptCapitalJ]) rn+ b (2 (-4+b)\[ScriptCapitalE]-sp \[ScriptCapitalJ]))};


\[CapitalPhi]r0[\[Chi]_]:=(2(sp \[ScriptCapitalE]+\[ScriptCapitalJ]) EllipticF[\[Chi],k0^2])/(Sqrt[1-\[ScriptCapitalE]^2] Sqrt[(r1-r3) (r2-r4)]);


\[CapitalPsi]r0[\[Chi]_]:=(2  \[ScriptCapitalE] \[ScriptCapitalJ])/(Sqrt[1-\[ScriptCapitalE]^2] Sqrt[(r1-r3) (r2-r4)]  (r2^2+\[ScriptCapitalJ]^2) (r3^2+\[ScriptCapitalJ]^2)) ( (r2-r3) \[ScriptCapitalJ] (r2 r3-\[ScriptCapitalJ]^2) Im[EllipticPi[((r1-r2) (r3-I \[ScriptCapitalJ]))/((r1-r3) (r2-I \[ScriptCapitalJ])),\[Chi],k0^2]]+r3^2 (r2^2+\[ScriptCapitalJ]^2) EllipticF[\[Chi],k0^2]+(r2-r3) (r2+r3) \[ScriptCapitalJ]^2 Re[EllipticPi[((r1-r2) (r3-I \[ScriptCapitalJ]))/((r1-r3) (r2-I \[ScriptCapitalJ])),\[Chi],k0^2]])/.{yr->Sin[\[Chi]]};


(* ::Subsection:: *)
(*Frequency*)


\[CurlyCapitalUpsilon]r=(\[Pi] Sqrt[(r1-r3) (r2-r4)] Sqrt[1-\[ScriptCapitalE]^2])/(2 EllipticK[k0^2]);
\[CurlyCapitalUpsilon]t=1/2 ((8-2 b+r1 (-r2+r3)+r3 (4+r2+r3)) \[ScriptCapitalE]+(2 ((-4+b) b \[ScriptCapitalE]-4 (-2+b) rp \[ScriptCapitalE]-b sp \[ScriptCapitalJ]+rp sp \[ScriptCapitalJ]))/((r3-rp) (-rn+rp))+(4 b^2 \[ScriptCapitalE]+2 rn (8 \[ScriptCapitalE]+sp \[ScriptCapitalJ])-2 b (4 (2+rn) \[ScriptCapitalE]+sp \[ScriptCapitalJ]))/((r3-rn) (rn-rp)))+((r1-r3) (r2-r4) \[ScriptCapitalE] EllipticE[k0^2])/(2 EllipticK[k0^2])+1/(2 EllipticK[k0^2]) (r2-r3) ((4+r1+r2+r3+r4) \[ScriptCapitalE] EllipticPi[(r1-r2)/(r1-r3),k0^2]+(2 (2 (-4+b) b \[ScriptCapitalE]-4 (-2+b) rn \[ScriptCapitalE]-b sp \[ScriptCapitalJ]+rn sp \[ScriptCapitalJ]) EllipticPi[((r1-r2) (r3-rn))/((r1-r3) (r2-rn)),k0^2])/((r2-rn) (-r3+rn) (rn-rp))+(2 ((-4+b) b \[ScriptCapitalE]-4 (-2+b) rp \[ScriptCapitalE]-b sp \[ScriptCapitalJ]+rp sp \[ScriptCapitalJ]) EllipticPi[((r1-r2) (r3-rp))/((r1-r3) (r2-rp)),k0^2])/((r2-rp) (-r3+rp) (-rn+rp)));
\[CurlyCapitalUpsilon]\[CurlyPhi]=sp \[ScriptCapitalE]+\[ScriptCapitalJ];
\[CurlyCapitalUpsilon]\[Psi]=(r3^2 \[ScriptCapitalE] \[ScriptCapitalJ])/(r3^2+\[ScriptCapitalJ]^2)+((r2-r3) \[ScriptCapitalE] \[ScriptCapitalJ]^2 ((r2 r3-\[ScriptCapitalJ]^2) Im[EllipticPi[((r1-r2) (r3-I \[ScriptCapitalJ]))/((r1-r3) (r2-I \[ScriptCapitalJ])),k0^2]]+(r2+r3) \[ScriptCapitalJ] Re[EllipticPi[((r1-r2) (r3-I \[ScriptCapitalJ]))/((r1-r3) (r2-I \[ScriptCapitalJ])),k0^2]]))/((r2^2+\[ScriptCapitalJ]^2) (r3^2+\[ScriptCapitalJ]^2) EllipticK[k0^2]);


(* ::Subsection:: *)
(*Linear shift*)


\[CurlyCapitalUpsilon]rb=Rational[1, 2] Pi ((r1b - r3b) (r2b - r4b))^Rational[1, 2] ((1 - \[ScriptCapitalE]2b)^Rational[1, 2]/EllipticK[kb02]);
\[CurlyCapitalUpsilon]rsp=Rational[1, 4] Pi ((r1b - r3b) (r2b - r4b))^Rational[-1, 2] ((-r3sb) (r2b - r4b) - (r1b - r3b) r4sb) ((1 - \[ScriptCapitalE]2b)^Rational[1, 2]/EllipticK[kb02]) + Rational[-1, 4] Pi ((r1b - r3b) (r2b - r4b))^Rational[1, 2] (1 - \[ScriptCapitalE]2b)^Rational[-1, 2] (\[ScriptCapitalE]2sb/EllipticK[kb02]) + Rational[-1, 4] (1 - kb02)^(-1) kb02^(-1) ks02 Pi ((r1b - r3b) (r2b - r4b))^Rational[1, 2] (1 - \[ScriptCapitalE]2b)^Rational[1, 2] EllipticK[kb02]^(-2) (EllipticE[kb02] - (1 - kb02) EllipticK[kb02]);


\[CapitalUpsilon]tb=Rational[1, 2] \[ScriptCapitalE]2b^Rational[1, 2] (8 - 2 b + r1b (-r2b + r3b) + r3b (4 + r2b + r3b) + 4 (r3b - rnb)^(-1) ((b^2 + 4 rnb - 2 b (2 + rnb))/(rnb - rpb)) + 2 (r3b - rpb)^(-1) (-rnb + rpb)^(-1) (b^2 + 8 rpb - 4 b (1 + rpb)) + (r1b - r3b) (r2b - r4b) (EllipticE[kb02]/EllipticK[kb02]) + (r2b - r3b) EllipticK[kb02]^(-1) ((4 + r1b + r2b + r3b + r4b) EllipticPi[hbr, kb02] + 4 (r2b - rnb)^(-1) (-r3b + rnb)^(-1) (b^2 + 4 rnb - 2 b (2 + rnb)) (rnb - rpb)^(-1) EllipticPi[hbrn, kb02] + 2 (r2b - rpb)^(-1) (-r3b + rpb)^(-1) (-rnb + rpb)^(-1) (b^2 + 8 rpb - 4 b (1 + rpb)) EllipticPi[hbrp, kb02]));
\[CapitalUpsilon]tsp=Rational[1, 2] ((-r3sb) (r3b - rnb)^(-2) (rnb - rpb)^(-1) (4 b^2 \[ScriptCapitalE]2b^Rational[1, 2] + 16 rnb \[ScriptCapitalE]2b^Rational[1, 2] - 8 b (2 + rnb) \[ScriptCapitalE]2b^Rational[1, 2]) - 2 r3sb (r3b - rpb)^(-2) (-rnb + rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[1, 2]) + (r1b r3sb + r3b r3sb + (4 + r2b + r3b) r3sb) \[ScriptCapitalE]2b^Rational[1, 2] + Rational[1, 2] (8 - 2 b + r1b (-r2b + r3b) + r3b (4 + r2b + r3b)) \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb + (r3b - rnb)^(-1) (rnb - rpb)^(-1) (2 b^2 \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb + 2 rnb (4 \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb + \[ScriptCapitalJ]2b^Rational[1, 2]) - 2 b (2 (2 + rnb) \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb + \[ScriptCapitalJ]2b^Rational[1, 2])) + 2 (r3b - rpb)^(-1) (-rnb + rpb)^(-1) (Rational[1, 2] (-4 + b) b \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - 2 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - b \[ScriptCapitalJ]2b^Rational[1, 2] + rpb \[ScriptCapitalJ]2b^Rational[1, 2])) + Rational[-1, 2] r3sb (r2b - r4b) \[ScriptCapitalE]2b^Rational[1, 2] (EllipticE[kb02]/EllipticK[kb02]) + Rational[-1, 2] (r1b - r3b) r4sb \[ScriptCapitalE]2b^Rational[1, 2] (EllipticE[kb02]/EllipticK[kb02]) + Rational[1, 4] (r1b - r3b) (r2b - r4b) \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb (EllipticE[kb02]/EllipticK[kb02]) + Rational[1, 4] kb02^(-1) ks02 (r1b - r3b) (r2b - r4b) \[ScriptCapitalE]2b^Rational[1, 2] ((EllipticE[kb02] - EllipticK[kb02])/EllipticK[kb02]) + Rational[-1, 4] (1 - kb02)^(-1) kb02^(-1) ks02 (r1b - r3b) (r2b - r4b) \[ScriptCapitalE]2b^Rational[1, 2] EllipticE[kb02] EllipticK[kb02]^(-2) (EllipticE[kb02] - (1 - kb02) EllipticK[kb02]) + Rational[-1, 2] r3sb EllipticK[kb02]^(-1) ((4 + r1b + r2b + r3b + r4b) \[ScriptCapitalE]2b^Rational[1, 2] EllipticPi[hbr, kb02] + 2 (r2b - rnb)^(-1) (-r3b + rnb)^(-1) (rnb - rpb)^(-1) (2 (-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rnb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrn, kb02] + 2 (r2b - rpb)^(-1) (-r3b + rpb)^(-1) (-rnb + rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrp, kb02]) + Rational[-1, 4] (1 - kb02)^(-1) kb02^(-1) ks02 (r2b - r3b) EllipticK[kb02]^(-2) (EllipticE[kb02] - (1 - kb02) EllipticK[kb02]) ((4 + r1b + r2b + r3b + r4b) \[ScriptCapitalE]2b^Rational[1, 2] EllipticPi[hbr, kb02] + 2 (r2b - rnb)^(-1) (-r3b + rnb)^(-1) (rnb - rpb)^(-1) (2 (-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rnb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrn, kb02] + 2 (r2b - rpb)^(-1) (-r3b + rpb)^(-1) (-rnb + rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrp, kb02]) + Rational[1, 2] (r2b - r3b) EllipticK[kb02]^(-1) ((r3sb + r4sb) \[ScriptCapitalE]2b^Rational[1, 2] EllipticPi[hbr, kb02] + Rational[1, 2] (4 + r1b + r2b + r3b + r4b) \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb EllipticPi[hbr, kb02] + (4 + r1b + r2b + r3b + r4b) \[ScriptCapitalE]2b^Rational[1, 2] (Rational[1, 2] (hbr - kb02)^(-1) ks02 ((-1 + kb02)^(-1) EllipticE[kb02] + EllipticPi[hbr, kb02]) + Rational[1, 2] (-1 + hbr)^(-1) hsr (-hbr + kb02)^(-1) (EllipticE[kb02] + hbr^(-1) (-hbr + kb02) EllipticK[kb02] + hbr^(-1) (hbr^2 - kb02) EllipticPi[hbr, kb02])) + 2 r3sb (r2b - rnb)^(-1) (-r3b + rnb)^(-2) (rnb - rpb)^(-1) (2 (-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rnb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrn, kb02] + 2 (r2b - rnb)^(-1) (-r3b + rnb)^(-1) (rnb - rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - 2 (-2 + b) rnb \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - b \[ScriptCapitalJ]2b^Rational[1, 2] + rnb \[ScriptCapitalJ]2b^Rational[1, 2]) EllipticPi[hbrn, kb02] + 2 (r2b - rnb)^(-1) (-r3b + rnb)^(-1) (rnb - rpb)^(-1) (2 (-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rnb \[ScriptCapitalE]2b^Rational[1, 2]) (Rational[1, 2] (hbrn - kb02)^(-1) ks02 ((-1 + kb02)^(-1) EllipticE[kb02] + EllipticPi[hbrn, kb02]) + Rational[1, 2] (-1 + hbrn)^(-1) hsrn (-hbrn + kb02)^(-1) (EllipticE[kb02] + hbrn^(-1) (-hbrn + kb02) EllipticK[kb02] + hbrn^(-1) (hbrn^2 - kb02) EllipticPi[hbrn, kb02])) + 2 r3sb (r2b - rpb)^(-1) (-r3b + rpb)^(-2) (-rnb + rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[1, 2]) EllipticPi[hbrp, kb02] + 2 (r2b - rpb)^(-1) (-r3b + rpb)^(-1) (-rnb + rpb)^(-1) (Rational[1, 2] (-4 + b) b \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - 2 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[-1, 2] \[ScriptCapitalE]2sb - b \[ScriptCapitalJ]2b^Rational[1, 2] + rpb \[ScriptCapitalJ]2b^Rational[1, 2]) EllipticPi[hbrp, kb02] + 2 (r2b - rpb)^(-1) (-r3b + rpb)^(-1) (-rnb + rpb)^(-1) ((-4 + b) b \[ScriptCapitalE]2b^Rational[1, 2] - 4 (-2 + b) rpb \[ScriptCapitalE]2b^Rational[1, 2]) (Rational[1, 2] (hbrp - kb02)^(-1) ks02 ((-1 + kb02)^(-1) EllipticE[kb02] + EllipticPi[hbrp, kb02]) + Rational[1, 2] (-1 + hbrp)^(-1) hsrp (-hbrp + kb02)^(-1) (EllipticE[kb02] + hbrp^(-1) (-hbrp + kb02) EllipticK[kb02] + hbrp^(-1) (hbrp^2 - kb02) EllipticPi[hbrp, kb02])));


\[CurlyCapitalUpsilon]\[CurlyPhi]b=Sqrt[\[ScriptCapitalJ]2b];
\[CurlyCapitalUpsilon]\[CurlyPhi]sp=Sqrt[\[ScriptCapitalE]2b]+\[ScriptCapitalJ]2sb/(2 Sqrt[\[ScriptCapitalJ]2b]);


\[CurlyCapitalUpsilon]\[Psi]b=(Sqrt[\[ScriptCapitalE]2b] Sqrt[\[ScriptCapitalJ]2b] (r3b^2+((r2b-r3b) Sqrt[\[ScriptCapitalJ]2b] ((r2b r3b-\[ScriptCapitalJ]2b) Im[EllipticPi[((r1b-r2b) (r3b-I Sqrt[\[ScriptCapitalJ]2b]))/((r1b-r3b) (r2b-I Sqrt[\[ScriptCapitalJ]2b])),kb02]]+(r2b+r3b) Sqrt[\[ScriptCapitalJ]2b] Re[EllipticPi[((r1b-r2b) (r3b-I Sqrt[\[ScriptCapitalJ]2b]))/((r1b-r3b) (r2b-I Sqrt[\[ScriptCapitalJ]2b])),kb02]]))/((r2b^2+\[ScriptCapitalJ]2b) EllipticK[kb02])))/(r3b^2+\[ScriptCapitalJ]2b);


\[Nu]nodal=2 \[Pi] (-1+(r3b^2+\[ScriptCapitalJ]2b)/(Sqrt[\[ScriptCapitalE]2b] (r3b^2+((r2b-r3b) Sqrt[\[ScriptCapitalJ]2b] ((r2b r3b-\[ScriptCapitalJ]2b) Im[EllipticPi[((r1b-r2b) (r3b-I Sqrt[\[ScriptCapitalJ]2b]))/((r1b-r3b) (r2b-I Sqrt[\[ScriptCapitalJ]2b])),kb02]]+(r2b+r3b) Sqrt[\[ScriptCapitalJ]2b] Re[EllipticPi[((r1b-r2b) (r3b-I Sqrt[\[ScriptCapitalJ]2b]))/((r1b-r3b) (r2b-I Sqrt[\[ScriptCapitalJ]2b])),kb02]]))/((r2b^2+\[ScriptCapitalJ]2b) EllipticK[kb02]))));
\[Nu]periBW=2 \[Pi] (-1+(2 Sqrt[\[ScriptCapitalJ]2b] EllipticK[kb02])/(\[Pi] Sqrt[(r1b-r3b) (r2b-r4b)] Sqrt[1-\[ScriptCapitalE]2b]));
\[Delta]\[Nu]peri=1/(\[Pi] (r1b-r3b) (r2b-r4b) (1-\[ScriptCapitalE]2b)) 8 EllipticK[kb02]^2 ((\[Pi] Sqrt[(r1b-r3b) (r2b-r4b)] Sqrt[1-\[ScriptCapitalE]2b] (Sqrt[\[ScriptCapitalE]2b]+\[ScriptCapitalJ]2sb/(2 Sqrt[\[ScriptCapitalJ]2b])))/(2 EllipticK[kb02])+Sqrt[\[ScriptCapitalJ]2b] (-((\[Pi] (-r3sb (r2b-r4b)-(r1b-r3b) r4sb) Sqrt[1-\[ScriptCapitalE]2b])/(4 Sqrt[(r1b-r3b) (r2b-r4b)] EllipticK[kb02]))+(\[Pi] Sqrt[(r1b-r3b) (r2b-r4b)] \[ScriptCapitalE]2sb)/(4 Sqrt[1-\[ScriptCapitalE]2b] EllipticK[kb02])+(ks02 \[Pi] Sqrt[(r1b-r3b) (r2b-r4b)] Sqrt[1-\[ScriptCapitalE]2b] (EllipticE[kb02]-(1-kb02) EllipticK[kb02]))/(4 (1-kb02) kb02 EllipticK[kb02]^2)));
\[Nu]peri=\[Nu]periBW+\[Delta]\[Nu]peri;



(* ::Subsection:: *)
(*Orbit*)


qr[\[Lambda]_]:=\[CurlyCapitalUpsilon]r \[Lambda] + qr0;
qt[\[Lambda]_]:=\[CurlyCapitalUpsilon]t \[Lambda] + qt0;
q\[CurlyPhi][\[Lambda]_]:=\[CurlyCapitalUpsilon]\[CurlyPhi] \[Lambda] + q\[CurlyPhi]0;
q\[Psi][\[Lambda]_]:=\[CurlyCapitalUpsilon]\[Psi] \[Lambda] + q\[Psi]0;


r0\[Lambda][\[Lambda]_]:=(r2 (-r1+r3)+(r1-r2) r3 (Sin@JacobiAmplitude[qr[\[Lambda]]/\[Pi] EllipticK[k0^2],k0^2])^2)/(-r1+r3+(r1-r2) (Sin@JacobiAmplitude[qr[\[Lambda]]/\[Pi] EllipticK[k0^2],k0^2])^2);
t0[\[Lambda]_]:=qt[\[Lambda]]+Tr0[JacobiAmplitude[qr[\[Lambda]]/\[Pi] EllipticK[k0^2],k0^2]]-Tr0[\[Pi]]/(2\[Pi]) qr[\[Lambda]];
\[CurlyPhi]0[\[Lambda]_]:=q\[CurlyPhi][\[Lambda]]+\[CapitalPhi]r0[JacobiAmplitude[qr[\[Lambda]]/\[Pi] EllipticK[k0^2],k0^2]]-\[CapitalPhi]r0[\[Pi]]/(2\[Pi]) qr[\[Lambda]];
\[Psi]0[\[Lambda]_]:=q\[Psi][\[Lambda]]+\[CapitalPsi]r0[JacobiAmplitude[qr[\[Lambda]]/\[Pi] EllipticK[k0^2],k0^2]]-\[CapitalPsi]r0[\[Pi]]/(2\[Pi]) qr[\[Lambda]];
\[Theta]0[\[Lambda]_]:=\[Pi]/2+(Sqrt[sn^2] Sqrt[(r0\[Lambda][\[Lambda]]^2+\[ScriptCapitalJ]^2)])/(r0\[Lambda][\[Lambda]] \[ScriptCapitalJ]) Sin[\[Psi]0[\[Lambda]]];


t0A[\[Lambda]_]:=Tr0[JacobiAmplitude[(Sqrt[(r1-r3) (r2-r4)] Sqrt[1-\[ScriptCapitalE]^2])/2 \[Lambda],k0^2]];


(* ::Section::Closed:: *)
(*Spacetime*)


(* ::Subsubsection:: *)
(*To the exact spacetime metric*)


(* ::Text:: *)
(*Spherically symmetric black hole*)


(* ::EquationNumbered:: *)
(*d s^2==-f r d t^2+(f d r^2)/r+r^2 (d \[Theta]^2+sin^2 \[Theta] d \[Phi]^2)*)


Options[ToSpacetime] = {"Spacetime" -> "UnKnow"};
SpacetimeSet={"UnKnow","Schwarzschild","Brane"};


ToSpacetime[OptionsPattern[]][exp_]:= Module[{spacetime,RepalceSet},
spacetime = OptionValue["Spacetime"];
If[MemberQ[spacetime, SpacetimeSet], 
Print["The spacetime metric is unknown"]];
If[spacetime == "UnKnow", RepalceSet={f->f}];
If[spacetime == "Schwarzschild", RepalceSet={f->fSh}];
If[spacetime == "Brane", RepalceSet={f->fShBW}];
exp/.RepalceSet
  ];


(* ::Section::Closed:: *)
(*Fluxes*)


(* ::Text:: *)
(*Reference*)


(* ::Text:: *)
(*[Gravitational_Peters_1964] P.C. Peters, Gravitational Radiation and the Motion of Two Point Masses, Phys. Rev. 136, B1224 (1964).*)


(* ::Text:: *)
(*[Gravitational_Peters_1963] P. C. Peters and J. Mathews, Gravitational Radiation from Point Masses in a Keplerian Orbit, Phys. Rev. 131, 435 (1963).*)


(* ::Subsection:: *)
(*Definition*)


(* ::Subsubsection:: *)
(*Define 3-dimensional space*)


Index3d:=Index3d=IndexRange[i,l];
DefManifold[M3,3,Index3d];


(* ::Subsubsection:: *)
(*Chart*)


DefChart[Euro,M3,{1,2,3},{x[],y[],z[]},ChartColor->Blue,FormatBasis->{"Partials","Differentials"}];


(* ::Subsubsection:: *)
(*ReducedMass*)


DefConstantSymbol[ReducedMass,PrintAs->"\[Mu]"];


(* ::Subsubsection:: *)
(*Metric*)


gEuro := gEuro= CTensor[{{1, 0, 0}, {0, 1,0},{0, 0 ,1}},{-Euro,-Euro}];


SetCMetric[gEuro,Euro,SignatureOfMetric->{3,0,0}];


(* ::Subsubsection:: *)
(*Fully antisymmetric tensors*)


epsilongEuor::usage = "epsilongEuor[i]:Fully antisymmetric tensors in three-dimensional Euclidean Spaces (Levi-Civita notation).";


epsilongEuor:=epsilongEuor=CTensor[LeviCivitaTensor[3],{-Euro,-Euro,-Euro}];


(* ::Subsubsection:: *)
(*The position vector of the test  particle*)


(* ::Input:: *)
(*Series[Sin[\[Pi]/2+\[Epsilon] ],{\[Epsilon] ,0,2}]*)
(*Series[Cos[\[Pi]/2+\[Epsilon] ],{\[Epsilon] ,0,2}]*)


(* ::Text:: *)
(*Here r[t] is the mass normalized r[t]*)


xPoint:=xPoint=CTensor[{M r[][t[]]  Cos[\[Phi][][t[]]],M r[][t[]]  Sin[\[Phi][][t[]]],- \[Epsilon] M r[][t[]]  \[Delta]\[Theta][][t[]]  },{-Euro}];


(* ::Text:: *)
(*Mass moment*)


QM:=QM=HeadOfTensor[ReducedMass xPoint[-i]xPoint[-j],{-i,-j}];


(* ::Subsubsection:: *)
(*The relation of energy \[ScriptCapitalE] and angular momentum \[ScriptCapitalJ] to  {e , p}*)


Options[EJTope] = {"Spacetime" ->"Schwarzschild"};
EJTope[OptionsPattern[]][exp_]:=Module[{spacetime,FK2,FK3,ReplaceSet,\[ScriptCapitalE]2Approxep,\[ScriptCapitalJ]2Approxep},
spacetime = OptionValue["Spacetime"];
FK2[r_]:=f[r]/ (r^2);
FK3[r_]:=(-2 f[r]+r Derivative[1][f][r])/r^2;
\[ScriptCapitalE]2Approxep=ToSpacetime["Spacetime"->spacetime]@rarpTope@((f[rperi] FK2[rapo]-f[rapo] FK2[rperi])/(FK2[rapo]-FK2[rperi])+(sp Sqrt[(f[rapo]-f[rperi]) (-f[rperi] FK2[rapo]+f[rapo] FK2[rperi])] (-FK2[rperi] FK3[rapo]+FK2[rapo] FK3[rperi]))/(FK2[rapo]-FK2[rperi])^2);
\[ScriptCapitalJ]2Approxep=ToSpacetime["Spacetime"->spacetime]@rarpTope@((-f[rapo]+f[rperi])/(FK2[rapo]-FK2[rperi])+1/(FK2[rapo]-FK2[rperi])^2 sp (-Sqrt[(f[rapo]-f[rperi]) (-f[rperi] FK2[rapo]+f[rapo] FK2[rperi])] FK3[rapo]+Sqrt[(f[rapo]-f[rperi]) (-f[rperi] FK2[rapo]+f[rapo] FK2[rperi])] FK3[rperi]));


ReplaceSet={\[ScriptCapitalE]^2->\[ScriptCapitalE]2Approxep,\[ScriptCapitalJ]^2->\[ScriptCapitalJ]2Approxep,\[ScriptCapitalE]->Sqrt[\[ScriptCapitalE]2Approxep],\[ScriptCapitalJ]->Sqrt[\[ScriptCapitalJ]2Approxep]};
exp/.ReplaceSet];


(* ::Input:: *)
(*FullSimplify[Series[EJTope["Spacetime" -> "Brane"]@(\[ScriptCapitalE]),{p,Infinity,3}]]*)
(*FullSimplify[Series[EJTope["Spacetime" -> "Brane"]@(\[ScriptCapitalJ]),{p,Infinity,0}]]*)


(* ::Subsubsection:: *)
(*Calculation of Fluxes *)


(* ::Text:: *)
(*Mark order symbol*)


DefConstantSymbol[OrderPN,PrintAs->"\!\(\*SubsuperscriptBox[\(h\), \(PN\), \(-1\)]\)"];


(* ::Text:: *)
(*Mark the lowest order*)


Mark[exp_]:=Module[{exp0=exp,ReplaceSet},
ReplaceSet={
p -> OrderPN p,
ParamD[t[]][psi[][t[]]] -> OrderPN^(-3/2) ParamD[t[]][psi[][t[]]],
ParamD[t[], t[]][psi[][t[]]] -> OrderPN^(-6/2) ParamD[t[], t[]][psi[][t[]]],
ParamD[t[], t[], t[]][psi[][t[]]] -> OrderPN^(-9/2) ParamD[t[], t[], t[]][psi[][t[]]],
r[][t[]]->OrderPN r[][t[]],
ParamD[t[]][r[][t[]]]->OrderPN^(-1/2) ParamD[t[]][r[][t[]]],
ParamD[t[], t[]][r[][t[]]]->OrderPN^(-4/2) ParamD[t[], t[]][r[][t[]]],
ParamD[t[], t[], t[]][r[][t[]]]->OrderPN^(-7/2) ParamD[t[], t[], t[]][r[][t[]]],
ParamD[t[]][\[Phi][][t[]]]->OrderPN^(-3/2) ParamD[t[]][\[Phi][][t[]]],
ParamD[t[], t[]][\[Phi][][t[]]]->OrderPN^(-6/2) ParamD[t[], t[]][\[Phi][][t[]]],
ParamD[t[], t[], t[]][\[Phi][][t[]]]->OrderPN^(-9/2) ParamD[t[], t[], t[]][\[Phi][][t[]]]
};
exp0/.ReplaceSet
];


(* ::Text:: *)
(*unmark*)


UnMark[exp_]:=Module[{exp0=exp,ReplaceSet},
ReplaceSet={OrderPN -> 1};
exp0/.ReplaceSet
]


(* ::Text:: *)
(*Order judgment and expansion*)


Options[OrderPNSeries] = {"Mark" ->"Off"};
OrderPNSeries[PN_,OptionsPattern[]][exp_]:=Module[{exp0=exp,PN0=PN,MarkOption,ReplaceSet},
MarkOption = OptionValue["Mark"];
If[MarkOption=="On",
Return[Normal@Simplify[Series[Mark@exp0,{sp,0,1},{OrderPN,Infinity,PN0},Assumptions->OrderPN>0&&M>0&&1>e>0&&p>0],1-LQGPolymeric>0&&1+LQGPolymeric>0&&OrderPN>0&&M>0&&1>e>0&&p>0&&-1+e^2<0]]
];
If[MarkOption=="Off",
Return[UnMark@Normal@Simplify[Series[Mark@exp0,{sp,0,1},{OrderPN,Infinity,PN0},Assumptions->OrderPN>0&&M>0&&1>e>0&&p>0],1-LQGPolymeric>0&&1+LQGPolymeric>0&&OrderPN>0&&M>0&&1>e>0&&p>0&&-1+e^2<0]]
];
]



(* ::Subsubsubsection:: *)
(*Reduces Subscript[\[Psi], r][t]  to a function of e,p*)


Options[Conpsitp] = {"Spacetime" ->"Schwarzschild"};

Conpsitp[n_,PN_,OptionsPattern[]][exp_]:=Module[{exp0=exp,PN0=PN,n0=n,spacetime,Ft,Fpsi,Fd\[Psi]dtPN,DFd\[Psi]dtPN,DDFd\[Psi]dtPN,ReplaceSet},
spacetime = OptionValue["Spacetime"];

If[!MemberQ[SpacetimeSet,spacetime], 
Print["Spacetime metric unknown, please select in " <>ToString[SpacetimeSet]<> "!"]];

If[MemberQ[SpacetimeSet,spacetime],
(*\:8fd0\:52a8\:65b9\:7a0b*) 
Ft=ParamExactBW[sp,sn,e,p,b,M]@ToSpacetime["Spacetime"->spacetime]@EJTope["Spacetime"->spacetime]@(\[ScriptCapitalE]/f[p/(1+e  Cos[psi[][t[]]])]+(\[ScriptCapitalJ] f'[p/(1+e Cos[psi[][t[]]])] sp)/(2 p/(1+e Cos[psi[][t[]]]) f[p/(1+e Cos[psi[][t[]]])]));
Fpsi=ParamExactBW[sp,sn,e,p,b,M]@ToSpacetime["Spacetime"->spacetime]@EJTope["Spacetime"->spacetime]@(1/M ((1+e Cos[psi[][t[]]])^2/(e p Sqrt[Sin[psi[][t[]]]^2]) Sqrt[\[ScriptCapitalE]^2-((\[ScriptCapitalJ]^2+(p/(1+e Cos[psi[][t[]]]))^2)f[p/(1+e Cos[psi[][t[]]])])/(p/(1+e Cos[psi[][t[]]]))^2+(sp \[ScriptCapitalJ] \[ScriptCapitalE](-2 f[p/(1+e Cos[psi[][t[]]])]+p/(1+e Cos[psi[][t[]]]) Derivative[1][f][p/(1+e Cos[psi[][t[]]])]))/(p/(1+e Cos[psi[][t[]]]))^2]));
(*\:7ea7\:6570\:5c55\:5f00\:6807\:8bb0*) 
Fd\[Psi]dtPN=If[!FreeQ[exp0,xAct`xTensor`ParamD[t[]][psi[][t[]]]]||!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[]][psi[][t[]]]]||!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][psi[][t[]]]],Print["Fd\[Psi]dtPN:"<>ToString[n0+1]];OrderPNSeries[n0+1][Fpsi/Ft]]; 
DFd\[Psi]dtPN=If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[]][psi[][t[]]]]||!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][psi[][t[]]]],Print["DFd\[Psi]dtPN:"<>ToString[n0+2]];OrderPNSeries[n0+2][ParamD[t[]][Fd\[Psi]dtPN]]];
DDFd\[Psi]dtPN=If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][psi[][t[]]]],Print["DDFd\[Psi]dtPN:"<>ToString[n0+4]]; OrderPNSeries[n0+4][ParamD[t[]][DFd\[Psi]dtPN]]];
(*Print[{Fd\[Psi]dtPN,DFd\[Psi]dtPN,DDFd\[Psi]dtPN}];*) 
ReplaceSet={r[][t[]]->p/(1+e Cos[psi[][t[]]]),
xAct`xTensor`ParamD[t[]][psi[][t[]]]->Fd\[Psi]dtPN,
xAct`xTensor`ParamD[t[], t[]][psi[][t[]]]->DFd\[Psi]dtPN,
xAct`xTensor`ParamD[t[], t[], t[]][psi[][t[]]]->DDFd\[Psi]dtPN} ;
Return[OrderPNSeries[PN0][exp/.ReplaceSet]]
];
];


(* ::Subsubsubsection:: *)
(*Reduce r, \[Phi] function to Subscript[\[Psi], r] function*)


Options[ConrtphitTopsit] = {"Spacetime" ->"Schwarzschild"};

ConrtphitTopsit[n_,PN_,OptionsPattern[]][exp_]:=Module[{exp0=exp,PN0=PN,n0=n,spacetime,dphidt0,dphidt,Ddphidt,DDdphidt,ReplaceSet},
spacetime = OptionValue["Spacetime"];

If[!MemberQ[SpacetimeSet,spacetime], 
Print["Spacetime metric unknown, please select in " <>ToString[SpacetimeSet]<> "!"]];


If[MemberQ[SpacetimeSet,spacetime],
dphidt0= ParamExactBW[sp,sn,e,p,b,M]@ToSpacetime["Spacetime"->spacetime]@EJTope["Spacetime"->spacetime]@(1/M (\[ScriptCapitalJ]/(p/(1+e Cos[psi[][t[]]]))^2+ (\[ScriptCapitalE] sp)/(p/(1+e Cos[psi[][t[]]]))^2)/(\[ScriptCapitalE]/f[p/(1+e Cos[psi[][t[]]])]+(\[ScriptCapitalJ] f'[p/(1+e Cos[psi[][t[]]])] sp)/(2 p/(1+e Cos[psi[][t[]]]) f[p/(1+e Cos[psi[][t[]]])])));
(*\:7ea7\:6570\:5c55\:5f00\:6807\:8bb0*) 
dphidt=OrderPNSeries[n0+1,"Mark" ->"Off"][dphidt0];
Ddphidt=If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[]][\[Phi][][t[]]]]||!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][\[Phi][][t[]]]],OrderPNSeries[n0+2,"Mark" ->"Off"][ParamD[t[]][dphidt]]];
DDdphidt=If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][\[Phi][][t[]]]],OrderPNSeries[n0+4,"Mark" ->"Off"][ParamD[t[]][Ddphidt]]];
ReplaceSet={ 
xAct`xTensor`ParamD[t[]][\[Phi][][t[]]]->dphidt,
xAct`xTensor`ParamD[t[], t[]][\[Phi][][t[]]]->Ddphidt,
xAct`xTensor`ParamD[t[], t[], t[]][\[Phi][][t[]]]->DDdphidt,
r[][t[]]->p/(1+e Cos[psi[][t[]]])
};
Return[OrderPNSeries[PN0,"Mark" ->"Off"][exp/.ReplaceSet]]
];
];



(* ::Subsubsubsection:: *)
(*Fluxes approximation results *)


Options[ConrtphitApprox] = {"Spacetime" ->"Schwarzschild"};
ConrtphitApprox[n_,PN_,OptionsPattern[]][exp_]:=Module[{exp0=exp,PN0=PN,n0=n,spacetime,eqdr,eqd2r,eqd3r,eqd\[Phi],eqd2\[Phi],eqd3\[Phi],ReplaceSet},
spacetime = OptionValue["Spacetime"];
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[]][r[][t[]]]],eqdr=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][xAct`xTensor`ParamD[t[]][r[][t[]]]]]; 
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[]][r[][t[]]]],eqd2r=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][xAct`xTensor`ParamD[t[], t[]][r[][t[]]]]]; 
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][r[][t[]]]],eqd3r=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][xAct`xTensor`ParamD[t[], t[], t[]][r[][t[]]]]]; 
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[]][\[Phi][][t[]]]],eqd\[Phi]=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][ParamD[t[]][\[Phi][][t[]]]]];  
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[]][\[Phi][][t[]]]],eqd2\[Phi]=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][ParamD[t[],t[]][\[Phi][][t[]]]]]; 
If[!FreeQ[exp0,xAct`xTensor`ParamD[t[], t[], t[]][\[Phi][][t[]]]],eqd3\[Phi]=Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@Conpsitp[n0,PN0,"Spacetime"->spacetime]@ConrtphitTopsit[n0,PN0,"Spacetime"->spacetime][ParamD[t[],t[],t[]][\[Phi][][t[]]]]]; 



ReplaceSet={
xAct`xTensor`ParamD[t[]][\[Phi][][t[]]]->eqd\[Phi],
xAct`xTensor`ParamD[t[], t[]][\[Phi][][t[]]]->eqd2\[Phi],
xAct`xTensor`ParamD[t[], t[], t[]][\[Phi][][t[]]]->eqd3\[Phi],
r[][t[]]->p/(1+e Cos[psi[][t[]]]),
xAct`xTensor`ParamD[t[]][r[][t[]]]->eqdr,
xAct`xTensor`ParamD[t[], t[]][r[][t[]]]->eqd2r,
xAct`xTensor`ParamD[t[], t[], t[]][r[][t[]]]->eqd3r
};
Return[OrderPNSeries[PN0,"Mark" ->"Off"][exp/.ReplaceSet]]
];
