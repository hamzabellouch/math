import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # Identifying normalized Hilbert pairings with local test integrals -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem normalizeLocalL2_smul (s : Set X) (hfin : μ s ≠ ∞)
    (a : ℝ) (f : Lp ℝ 2 (μ.restrict s)) :
    normalizeLocalL2 μ s hfin (a • f) = a • normalizeLocalL2 μ s hfin f := by
  exact smul_comm _ _ _

theorem normalized_inner (s : Set X) (hfin : μ s ≠ ∞)
    (f g : Lp ℝ 2 (μ.restrict s)) :
    ⟪normalizeLocalL2 μ s hfin f, normalizeLocalL2 μ s hfin g⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s, f x * g x ∂μ := by
  have hscalar : (‖restrictedOne μ s hfin‖⁻¹) ^ 2 = (μ.real s)⁻¹ := by
    rw [inv_pow, restrictedOne_norm, Real.sq_sqrt (by positivity)]
  simp only [normalizeLocalL2, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, hscalar, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

theorem normalized_inner_of_representatives (s : Set X) (hfin : μ s ≠ ∞)
    (f g : Lp ℝ 2 (μ.restrict s)) (F G : X → ℝ)
    (hf : f =ᵐ[μ.restrict s] F) (hg : g =ᵐ[μ.restrict s] G) :
    ⟪normalizeLocalL2 μ s hfin f, normalizeLocalL2 μ s hfin g⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s, F x * G x ∂μ := by
  rw [normalized_inner]
  congr 1
  exact integral_congr_ae (hf.mul hg)

theorem normalized_norm_le_of_bound (s : Set X) (hfin : μ s ≠ ∞)
    (f : Lp ℝ 2 (μ.restrict s)) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ.restrict s, |f x| ≤ C) :
    ‖normalizeLocalL2 μ s hfin f‖ ≤ C := by
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hi : (∫ x in s, (f x) ^ 2 ∂μ) ≤ C ^ 2 * μ.real s := by
    have hb : ∀ᵐ x ∂μ.restrict s, (f x) ^ 2 ≤ C ^ 2 := by
      filter_upwards [hf] with x hx
      nlinarith [abs_le.mp hx, sq_nonneg (f x)]
    have hh := integral_mono_ae (Lp.memLp f).integrable_sq (integrable_const (C ^ 2)) hb
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm] using hh
  apply (sq_le_sq₀ (norm_nonneg _) hC).mp
  rw [normalizeLocalL2_norm_sq]
  by_cases hz : μ.real s = 0
  · simp only [hz, inv_zero, zero_mul]
    positivity
  · calc
      _ ≤ (μ.real s)⁻¹ * (C ^ 2 * μ.real s) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = C ^ 2 := by field_simp

end RegularPointCoordinates

end

end OAI
