import OAI.Probability.ClassicalON.MomentCone

namespace OAI

universe uI uV uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {I : Type uI} {X : Type uX} [Fintype V] [DecidableEq V]

def retainedIndices (v : V) (l : List (V×I)) : List I :=
  l.filterMap (fun p => if p.1=v then some p.2 else none)

theorem site_grouping (a : I → X → ℝ) (l : List (V×I)) (x : V → X) :
    (l.map (fun p => a p.2 (x p.1))).prod =
      ∏ v,((retainedIndices v l).map (fun i => a i (x v))).prod := by
  induction l with
  | nil => simp [retainedIndices]
  | cons p l ih =>
    have hv (v : V) :
        ((retainedIndices v (p::l)).map (fun i => a i (x v))).prod =
        (if p.1=v then a p.2 (x p.1) else 1)*
          ((retainedIndices v l).map (fun i => a i (x v))).prod := by
      by_cases h : p.1=v
      · subst v; simp [retainedIndices]
      · simp [retainedIndices,h]
    simp only [List.map_cons,List.prod_cons,ih,hv,Finset.prod_mul_distrib]
    congr 1
    simp

theorem independent_moments_nonneg [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : I → X → ℝ)
    (hm : ∀ l : List I,0≤∫ x,(l.map (fun i => a i x)).prod ∂μ)
    (l : List (V×I)) :
    0≤∫ x : V → X,(l.map (fun p => a p.2 (x p.1))).prod ∂Measure.pi (fun _ => μ) := by
  simp_rw [site_grouping a l]
  rw [integral_fintype_prod_eq_prod (fun v x =>
    (List.map (fun i => a i x) (retainedIndices v l)).prod)]
  exact Finset.prod_nonneg (fun v _ => hm (retainedIndices v l))

end ClassicalON

end

end OAI
