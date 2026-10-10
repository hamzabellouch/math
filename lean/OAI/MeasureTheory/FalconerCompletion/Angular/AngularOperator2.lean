import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.StationaryInverseUnit3

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def angularOperatorND (A : V →L[ℝ] V) : Module.End ℂ (SmoothFunctionND V) where
  toFun b := ⟨angularDerivativeND A b.1,angularDerivativeND_contDiff A b.2⟩
  map_add' b c := Subtype.ext (angularDerivativeND_add A b.2 c.2)
  map_smul' z b := Subtype.ext (angularDerivativeND_const_mul A b.2 z)

lemma smoothFunctionND_contDiff (f : SmoothFunctionND V) : ContDiff ℝ ∞ f.1 := f.2

noncomputable def smoothMulND (f g : SmoothFunctionND V) : SmoothFunctionND V :=
  ⟨fun x => f.1 x*g.1 x,(smoothFunctionND_contDiff f).mul (smoothFunctionND_contDiff g)⟩

lemma angularOperatorND_mul (A : V →L[ℝ] V) (f g : SmoothFunctionND V) :
    angularOperatorND A (smoothMulND f g)=
      smoothMulND (angularOperatorND A f) g+smoothMulND f (angularOperatorND A g) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun x => f.1 x*g.1 x) x (A x) = _
  rw [fderiv_fun_mul ((smoothFunctionND_contDiff f).differentiable (by simp) x) ((smoothFunctionND_contDiff g).differentiable (by simp) x)]
  change f.1 x * fderiv ℝ g.1 x (A x) + g.1 x * fderiv ℝ f.1 x (A x) =
    fderiv ℝ f.1 x (A x) * g.1 x + f.1 x * fderiv ℝ g.1 x (A x)
  ring

noncomputable def angularWordOperatorND : List (V →L[ℝ] V) → Module.End ℂ (SmoothFunctionND V)
  | [] => 1
  | A::L => angularOperatorND A * angularWordOperatorND L

lemma angularWordOperatorND_append (L K : List (V →L[ℝ] V)) :
    angularWordOperatorND (L++K)=angularWordOperatorND L*angularWordOperatorND K := by
  induction L with
  | nil => simp [angularWordOperatorND]
  | cons A L ih => simp [angularWordOperatorND,ih,mul_assoc]

def angularWordSplitsND {α : Type*} : List α → List (List α × List α)
  | [] => [([],[])]
  | A::L => (angularWordSplitsND L).flatMap (fun p => [(A::p.1,p.2),(p.1,A::p.2)])

lemma angularWordSplitsND_length {α : Type*} (L : List α) :
    (angularWordSplitsND L).length=2^L.length := by
  induction L with
  | nil => simp [angularWordSplitsND]
  | cons A L ih => simp [angularWordSplitsND,List.length_flatMap,ih,pow_succ,Nat.mul_comm]

lemma angularWordSplitsND_budget {α : Type*} (L : List α) (p : List α × List α)
    (hp : p ∈ angularWordSplitsND L) : p.1.length+p.2.length=L.length := by
  induction L generalizing p with
  | nil => simp only [angularWordSplitsND,List.mem_singleton] at hp; subst p; rfl
  | cons A L ih =>
    obtain ⟨q,hq,hpq⟩ := List.mem_flatMap.mp hp
    have hh := ih q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hpq
    rcases hpq with rfl|rfl <;> simp only [List.length_cons] <;> omega

lemma angularWordOperatorND_leibniz (L : List (V →L[ℝ] V)) (f g : SmoothFunctionND V) :
    angularWordOperatorND L (smoothMulND f g)=
      ((angularWordSplitsND L).map (fun p =>
        smoothMulND (angularWordOperatorND p.1 f) (angularWordOperatorND p.2 g))).sum := by
  induction L with
  | nil => simp [angularWordOperatorND,angularWordSplitsND]
  | cons A L ih =>
    change angularOperatorND A (angularWordOperatorND L (smoothMulND f g)) = _
    rw [ih,map_list_sum]
    simp only [List.map_map,Function.comp_def,angularOperatorND_mul,angularWordSplitsND,
      List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      angularWordOperatorND,Module.End.mul_apply]

lemma angularWordOperatorND_support (L : List (V →L[ℝ] V)) (b : SmoothFunctionND V) :
    tsupport (angularWordOperatorND L b).1 ⊆ tsupport b.1 := by
  induction L with
  | nil => simp [angularWordOperatorND]
  | cons A L ih =>
    exact (tsupport_angularDerivativeND_subset A (angularWordOperatorND L b).1).trans ih

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
