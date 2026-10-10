import Mathlib
import OAI.Probability.SKGap.Localization.PhiRegularity
import OAI.Probability.SKGap.Stability.ImplicitNode

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

abbrev InitialArgs := Args (ι:=Unit) (κ:=Bool)
def initialKernel (f : KernelExpr) (r : ℝ) (u : InitialArgs) : ℝ :=
  f.eval (u (.inl ())) r (u (.inr false))
def initialGradient (f : KernelExpr) (r : ℝ) (u : InitialArgs) : InitialArgs→L[ℝ]ℝ :=
  (f.gradient (phiSelect () false u+(0,(r,0)))).comp (phiSelect () false)
def phiExpr : KernelExpr := .atom 0 0 false

lemma initialKernel_phi (r : ℝ) (u : InitialArgs) :
    initialKernel phiExpr r u=phi (u (.inl ())) r (u (.inr false)) := moment_base _ _ _
lemma phiExpr_dz (z r a : ℝ) : phiExpr.dz.eval z r a=phiZ z r a := by
  have H:=phiExpr.hasDerivAt_z z r a
  have He : phiExpr.eval=phi := funext fun _=>funext fun _=>funext fun _=>moment_base _ _ _
  rw [He] at H
  exact H.unique (phi_hasDerivAt z r a)

lemma initialGradient_primary (f : KernelExpr) (r : ℝ) (u : InitialArgs) :
    partialAt (initialGradient f r u) (.inl ())=f.dz.eval (u (.inl ())) r (u (.inr false)) := by
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3]

lemma initialKernel_hasFDerivAt (f : KernelExpr) (r : ℝ) (u : InitialArgs) :
    HasFDerivAt (initialKernel f r) (initialGradient f r u) u := by
  have H:=(f.hasFDerivAt_eval (phiSelect () false u+(0,(r,0)))).comp u
    ((phiSelect () false).hasFDerivAt.add_const (0,(r,0)))
  convert! H using 1
  ext v
  simp [initialKernel,eval3,phiSelect_apply]

def literalInitial (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) : OrdinaryData n Unit Bool Bool where
  J:=J
  j:=j
  H:=fun _=>z
  predecessor:=fun _=>m
  θ:=fun b x=>if b then d*c x else a x
  seed:=fun b i=>if b then Real.tanh (r i)/d else e i
  seedFunction:=fun _ b i u=>if b then -j*u (.inr true)*initialKernel phiExpr (r i) u else initialKernel f (r i) u
  seedDerivative:=fun _ b i u=>if b then (-j) •
    (u (.inr true) • initialGradient phiExpr (r i) u+
      (initialKernel phiExpr (r i) u) • ContinuousLinearMap.proj (.inr true))
    else initialGradient f (r i) u
  auxFunction:=fun _ _ i u=>initialKernel phiExpr (r i) u
  auxDerivative:=fun _ _ i u=>initialGradient phiExpr (r i) u

lemma literalInitial_coefficient (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitCoefficient x i=phi (z x i) (r i) (a x) := by
  simp [OrdinaryData.implicitCoefficient,OrdinaryData.auxCoefficient,literalInitial,
    coefficient,initialKernel_phi,localArgs]

lemma literalInitial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x i=
      f.eval (z x i) (r i) (a x)*e i+
        phi (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp [OrdinaryData.sourceOf,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,
    literalInitial,coefficient,initialKernel,phiExpr,KernelExpr.eval,moment_base,localArgs]
  field_simp
  ring

lemma literalInitial_partial (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitPartial y x i=
      f.dz.eval (z x i) (r i) (a x)*e i+
        phiZ (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp only [OrdinaryData.implicitPartial,OrdinaryData.partialOf,OrdinaryData.seedPartial,
    OrdinaryData.auxPartial,localPartial,literalInitial,Fintype.sum_bool,Fin.sum_univ_one]
  simp only [Bool.false_eq_true,↓reduceIte,initialGradient_primary]
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3,localArgs,phiExpr_dz]
  field_simp
  ring

end SKGapCutoff.Recipe

end
end

end OAI
