import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! Local parameter-space counts for all tubes through a regular row.
This proves the 2s-dimensional count in the product-structure reduction. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem row_tube_parameter_near {δ r y : ℝ} (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (hy : |y| ≤ 1) {x l z : Space 2} (hx : x 0 = y)
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) (hlz : dist l z ≤ r) :
    dist x (rowPoint y (lineParameterProjection y z)) ≤ 4*r := by
  rw [row_dist_projection hx]
  have hp := tube_projection_near hδ hl hi
  rw [hx] at hp
  calc
    _ ≤ |x 1-lineParameterProjection y l|+
        |lineParameterProjection y l-lineParameterProjection y z| := abs_sub_le _ _ _
    _ ≤ _ := by linarith [lineParameterProjection_dist hy l z]

theorem row_tube_ball_count {δ y s KP KT M r : ℝ} (hδ : 0 < δ)
    (hδr : δ ≤ r) (hr : 4*r ≤ 1) (hy : |y| ≤ 1) (hKT : 0 ≤ KT) (hM0 : 0 ≤ M)
    {P : Finset (Space 2)} (hrow : ∀ x ∈ P, x 0 = y)
    (hP : NormalizedFiniteBallBound δ s KP P) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hT : ∀ x ∈ P, NormalizedFiniteBallBound δ s KT (T x))
    (hM : ∀ x ∈ P, ((T x).card : ℝ) ≤ M)
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) (z : Space 2) :
    (((P.biUnion T).filter fun l => dist l z ≤ r).card : ℝ) ≤
      (KP*(4*r)^s*(P.card : ℝ))*(KT*r^s*M) := by
  classical
  let S := P.filter fun x => dist x (rowPoint y (lineParameterProjection y z)) ≤ 4*r
  let U := fun x => (T x).filter fun l => dist l z ≤ r
  have hsub : (P.biUnion T).filter (fun l => dist l z ≤ r) ⊆ S.biUnion U := by
    intro l hl
    obtain ⟨hlP,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hlP
    refine Finset.mem_biUnion.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,
      Finset.mem_filter.mpr ⟨hxl,hlr⟩⟩
    exact row_tube_parameter_near hδ.le hδr hy (hrow x hx)
      (hchart x hx l hxl).1 (hinc x hx l hxl) hlr
  have hr0 : 0 < r := hδ.trans_le hδr
  have hc : (S.card : ℝ) ≤ KP*(4*r)^s*(P.card : ℝ) :=
    hP _ (4*r) (by linarith) hr
  calc
    _ ≤ ((S.biUnion U).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ x ∈ S, ((U x).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, KT*r^s*M := by
      apply Finset.sum_le_sum
      intro x hx
      have hxP := (Finset.mem_filter.mp hx).1
      exact (hT x hxP z r hδr (by linarith)).trans
        (mul_le_mul_of_nonneg_left (hM x hxP)
          (mul_nonneg hKT (Real.rpow_nonneg hr0.le _)))
    _ = (S.card : ℝ)*(KT*r^s*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg
      (mul_nonneg hKT (Real.rpow_nonneg hr0.le _)) hM0)

end Falconer

end OAI
