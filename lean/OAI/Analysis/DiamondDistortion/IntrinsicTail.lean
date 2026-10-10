import OAI.Analysis.DiamondDistortion.FullDual

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

open scoped Classical
open Filter Topology

namespace Ancestry
variable {ι : Type*} [A : Ancestry ι]

lemma intrinsic_tail
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ}
    {x y : A.segments.Dual} (hx : A.segments.headDual H x=x)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) :
    ‖A.segments.tailDual H y‖ ≤ 2*Real.sqrt (R^2-‖x‖^2) := by
  have hs := A.intrinsic_tail_sq hfin hH ((norm_nonneg _).trans hplus)
    (fun v hv => by
      have h := congrArg (fun z : A.segments.Dual => z (A.segments.unitVector v)) hx
      rw [A.segments.headDual_unit,ite_eq_right hv] at h
      exact h.symm) hplus hminus
  have hd : 0 ≤ R^2-‖x‖^2 := by nlinarith [sq_nonneg ‖A.segments.tailDual H y‖]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*Real.sqrt (R^2-‖x‖^2))).mp
  nlinarith [Real.sq_sqrt hd]
end Ancestry

/-- Exact intrinsic input for the headline, on the whole finite-forest dual. -/
theorem forest_intrinsic_tail {H : Finset ForestNode}
    (hH : Ancestry.Ancestral (A := forestAncestry) (H : Set ForestNode)) {R : ℝ}
    {x y : ForestDual} (hx : forestSegments.headDual H x=x)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖forestSegments.tailDual H y‖ ≤ 2*Real.sqrt (R^2-‖x‖^2) :=
  Ancestry.intrinsic_tail (A := forestAncestry) forest_finite_heads hH hx hp hm

/-- The intrinsic input for the infinite-height coordinate predual is proved
    even in the ambient dual. Only finite-head center approximation in the graph
    deduction is restricted to the closed coordinate span. -/
theorem infinite_intrinsic_tail {H : Finset (List ℕ)}
    (hH : Ancestry.Ancestral (A := infiniteAncestry) (H : Set (List ℕ))) {R : ℝ}
    {x y : infiniteSegments.Dual} (hx : infiniteSegments.headDual H x=x)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖infiniteSegments.tailDual H y‖ ≤ 2*Real.sqrt (R^2-‖x‖^2) :=
  Ancestry.intrinsic_tail (A := infiniteAncestry) infinite_finite_heads hH hx hp hm

end DiamondDistortion

end

end OAI
