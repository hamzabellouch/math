import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteShellTail
import OAI.Analysis.RieszRectifiability.Kernel.FarHeightTail

namespace OAI

/-!
# Annular integrability for height-tail estimates

Lipschitz height functions are bounded on each dyadic annulus. The finite
annular mass supplied by upper growth then gives the square integrability
needed to apply shell estimates in the height-tail decomposition.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_height_memLp_on_annulus {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    MemLp w 2 (μ.restrict (dyadicAnnulus a R k)) := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable
    ((K : ℝ) * (R * 2 ^ (k + 1)) + |w a|)
  filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
  rw [Real.norm_eq_abs]
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have habs : |w y| ≤ |w y - w a| + |w a| := by
    simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
  exact habs.trans (add_le_add
    (hdiff.trans (mul_le_mul_of_nonneg_left hy.2.le K.coe_nonneg)) le_rfl)

theorem weighted_height_closed_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((K : ℝ) + |w a| / R) * (2 * (C * 2 ^ m / R)) := by
  obtain ⟨hweight, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => |w y| * inverseDistancePow (m + 2) a y) :=
    hw.continuous.measurable.abs.mul (inverseDistancePow_measurable _ _)
  have hpoint (y : Ambient d) (hy : y ∈ closedExterior a R) :
      |w y| * inverseDistancePow (m + 2) a y ≤
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y := by
    have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
    calc
      _ ≤ (((K : ℝ) + |w a| / R) * dist a y) * inverseDistancePow (m + 2) a y :=
        mul_le_mul_of_nonneg_right (lipschitz_height_radial_bound w K hw a y R hR hy)
          (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        unfold inverseDistancePow
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        field_simp
  have hi : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ := by
    apply (hweight.const_mul ((K : ℝ) + |w a| / R)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
    exact hpoint y hy
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R,
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi (hweight.const_mul _)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact hpoint y hy
    _ = ((K : ℝ) + |w a| / R) * (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

theorem finiteShellRegion_union_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N ∪ closedExterior a (R * 2 ^ N) = closedExterior a R := by
  rw [finiteShellRegion_eq a R hR N]
  have hRT : R ≤ R * (2 : ℝ) ^ N := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  ext y
  change (R ≤ dist a y ∧ dist a y < R * 2 ^ N) ∨ R * 2 ^ N ≤ dist a y ↔ R ≤ dist a y
  constructor
  · rintro (h | h)
    · exact h.1
    · exact hRT.trans h
  · intro hy
    by_cases h : dist a y < R * 2 ^ N
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (le_of_not_gt h)

theorem finiteShellRegion_disjoint_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    Disjoint (finiteShellRegion a R N) (closedExterior a (R * 2 ^ N)) := by
  rw [finiteShellRegion_eq a R hR N]
  exact Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hy) hx.2)

theorem improved_weighted_height_tail_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) +
          ((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N))) := by
  obtain ⟨hIfin, hbfin⟩ := finite_shell_weighted_height_bound m C B μ hg hCB a R hR N w
    (fun k _ => lipschitz_height_memLp_on_annulus m C μ hg w K hw a R hR k) δ b hδ hb0 hb2 hsecond
  obtain ⟨hItail, hbtail⟩ := weighted_height_closed_tail_bound m C μ hg w K hw a (R * 2 ^ N) (by positivity)
  rw [← finiteShellRegion_union_closedExterior a R hR N]
  refine ⟨hIfin.union hItail, ?_⟩
  rw [setIntegral_union (finiteShellRegion_disjoint_closedExterior a R hR N)
    (closedExterior_measurable a (R * 2 ^ N)) hIfin hItail]
  exact add_le_add hbfin hbtail

end

end RieszRectifiability

end OAI
