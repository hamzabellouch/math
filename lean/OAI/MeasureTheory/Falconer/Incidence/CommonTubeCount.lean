import OAI.MeasureTheory.Falconer.Geometry.TwoPointTubeGeometry
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! The normalized two-point common-tube kernel in the actual line chart. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem common_tube_card_bound {δ r b K : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    (hR1 : 80*δ/r ≤ 1) (hK : 0 ≤ K)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hxy : r ≤ dist x y) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/r)^b*(T.card : ℝ) := by
  let S := T.filter (fun l => TubeIncident δ y l)
  by_cases hS : S.Nonempty
  · obtain ⟨m,hm⟩ := hS
    have hmT := (Finset.mem_filter.mp hm).1
    have hmy := (Finset.mem_filter.mp hm).2
    have hsub : S ⊆ T.filter (fun l => dist l m ≤ 80*δ/r) := by
      intro l hl
      obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,two_point_tube_parameters_close hδ.le hr hr1 hsmall
        hx0 (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy⟩
    have hR0 : δ ≤ 80*δ/r := by
      apply (le_div_iff₀ hr).2
      nlinarith [mul_le_mul_of_nonneg_left hr1 hδ.le]
    exact (show (S.card : ℝ) ≤ (T.filter (fun l => dist l m ≤ 80*δ/r)).card by
      exact_mod_cast Finset.card_le_card hsub).trans (hball m _ hR0 hR1)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (Nat.cast_nonneg _)

end Falconer

end OAI
