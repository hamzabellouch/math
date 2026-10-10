import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShellHeightL1
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds

namespace OAI

/-!
# Weighted height bounds on dyadic shells

Square-integrable height bounds on each shell control integrals weighted by
inverse powers of distance. The dyadic coefficient identity expresses these
estimates in the geometric form needed for tail bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem dyadic_weighted_height_coefficient (m k : ℕ) (B δ R b : ℝ) (hR : 0 < R) :
    ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) =
      (B * δ / R) * (b / 2) ^ k := by
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, div_pow]
  field_simp

theorem shell_weighted_height_integrable_and_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (dyadicAnnulus a R k) μ ∧
      (∫ y in dyadicAnnulus a R k, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) * (b / 2) ^ k := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hfirst := (hw.integrable (by norm_num)).abs
  have hpoint : ∀ᵐ y ∂μ.restrict (dyadicAnnulus a R k),
      ‖inverseDistancePow (m + 2) a y‖ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ := by
    filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
    exact inverseDistancePow_bound_on_annulus (m + 2) a R hR k y hy
  have hi := hfirst.mul_bdd (inverseDistancePow_measurable (m + 2) a).aestronglyMeasurable hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in dyadicAnnulus a R k, ((R * 2 ^ k) ^ (m + 2))⁻¹ * |w y| ∂μ := by
      apply integral_mono_ae hi (hfirst.const_mul _)
      filter_upwards [hpoint] with y hy
      rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)] at hy
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hy (abs_nonneg (w y))
    _ = ((R * 2 ^ k) ^ (m + 2))⁻¹ * (∫ y in dyadicAnnulus a R k, |w y| ∂μ) :=
      integral_const_mul _ _
    _ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) :=
      mul_le_mul_of_nonneg_left (shell_height_l1_bound m C B μ hg hCB a R hR k w hw δ b hδ hb hsecond)
        (by positivity)
    _ = _ := dyadic_weighted_height_coefficient m k B δ R b hR

def finiteShellRegion {d : ℕ} (a : Ambient d) (R : ℝ) (N : ℕ) : Set (Ambient d) :=
  ⋃ k ∈ Finset.range N, dyadicAnnulus a R k

theorem finiteShellRegion_eq {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N = {y | R ≤ dist a y ∧ dist a y < R * 2 ^ N} := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
    have hlow : R ≤ R * (2 : ℝ) ^ k := by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hhigh : R * (2 : ℝ) ^ (k + 1) ≤ R * 2 ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) hR.le
    exact ⟨hlow.trans hyk.1, hyk.2.trans_le hhigh⟩
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((closedExterior_subset_iUnion_dyadicAnnulus a R hR) hy.1)
    have hkN : k < N := by
      by_contra h
      have hp : R * (2 : ℝ) ^ N ≤ R * 2 ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt h)) hR.le
      exact (not_lt_of_ge (hp.trans hk.1)) hy.2
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkN, hk⟩

theorem finite_shell_weighted_height_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (w : Ambient d → ℝ) (hw : ∀ k < N, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (finiteShellRegion a R N) μ ∧
      (∫ y in finiteShellRegion a R N, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) := by
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hI (k : ℕ) (hk : k ∈ Finset.range N) :=
    (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
      (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).1
  have hratio : ‖b / 2‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; linarith
  have hgeo := summable_geometric_of_norm_lt_one hratio
  constructor
  · exact integrableOn_finset_iUnion.mpr hI
  · rw [finiteShellRegion, integral_biUnion_finset (Finset.range N)
      (fun k _ => dyadicAnnulus_measurable a R k)
      (fun k _ l _ hkl => dyadicAnnulus_disjoint a R hR hkl) hI]
    calc
      _ ≤ ∑ k ∈ Finset.range N, (B * δ / R) * (b / 2) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
          (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).2
      _ = (B * δ / R) * ∑ k ∈ Finset.range N, (b / 2) ^ k := by rw [Finset.mul_sum]
      _ ≤ (B * δ / R) * ∑' k : ℕ, (b / 2) ^ k :=
        mul_le_mul_of_nonneg_left (hgeo.sum_le_tsum (Finset.range N) (fun k _ => by positivity))
          (by positivity)
      _ = _ := by rw [tsum_geometric_of_norm_lt_one hratio]; rfl

end

end RieszRectifiability

end OAI
