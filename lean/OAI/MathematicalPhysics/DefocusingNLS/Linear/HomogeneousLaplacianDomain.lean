import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLowerOrder
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalLaplacian

namespace OAI

/-! # Two extra Fourier orders put the physical Laplacian in Y -/

open MeasureTheory
open scoped Laplacian RealInnerProductSpace

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousFourierWeight_laplacian (a k : ℝ) (ha : 0 < a) (hk : 8 < k) (ξ : E) :
    homogeneousFourierWeight a k ξ * ‖ξ‖ ^ 4 ≤ 2 * homogeneousFourierWeight a (k + 2) ξ := by
  by_cases hzero : ‖ξ‖ = 0
  · simp only [homogeneousFourierWeight, hzero, zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    positivity
  have hr : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  have hlo : ‖ξ‖ ^ (2 * (6 - a) + 4) ≤
      ‖ξ‖ ^ (2 * (6 - a)) + ‖ξ‖ ^ (2 * (k + 2)) := by
    by_cases h : ‖ξ‖ ≤ 1
    · exact (Real.rpow_le_rpow_of_exponent_ge hr h (by linarith)).trans
        (le_add_of_nonneg_right (by positivity))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith)).trans
        (le_add_of_nonneg_left (by positivity))
  have hhi : 2 * k + 4 = 2 * (k + 2) := by ring
  unfold homogeneousFourierWeight
  rw [mul_assoc, add_mul, ← Real.rpow_natCast ‖ξ‖ 4, ← Real.rpow_add hr,
    ← Real.rpow_add hr]
  norm_num only [Nat.cast_ofNat]
  rw [hhi]
  have hnon : 0 ≤ ‖ξ‖ ^ (2 * (6 - a)) := by positivity
  have hsum : ‖ξ‖ ^ (2 * (6 - a) + 4) + ‖ξ‖ ^ (2 * (k + 2)) ≤
      2 * (‖ξ‖ ^ (2 * (6 - a)) + ‖ξ‖ ^ (2 * (k + 2))) := by linarith
  calc
    _ ≤ ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (2 * (‖ξ‖ ^ (2 * (6 - a)) + ‖ξ‖ ^ (2 * (k + 2)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem homogeneous_memLp_laplacian (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a (k + 2)) :
    MemLp (fun ξ => (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ) 2 (homogeneousFourierMeasure a k) := by
  have hk2 : 8 < k + 2 := by linarith
  have hm := (continuous_homogeneousFourierWeight a k ha1 hk).measurable
  have hm2 := (continuous_homogeneousFourierWeight a (k + 2) ha1 hk2).measurable
  have hu := (Lp.memLp u).aestronglyMeasurable.mono_ac
    (volume_absolutelyContinuous_homogeneousFourierMeasure a (k + 2) ha1 hk2)
  have hmul : AEStronglyMeasurable (fun ξ : E => (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ) volume :=
    (by fun_prop : Continuous (fun ξ : E => (-(‖ξ‖ ^ 2 : ℝ) : ℂ))).aestronglyMeasurable.mul hu
  apply (memLp_two_iff_integrable_sq_norm
    (hmul.mono_ac (withDensity_absolutelyContinuous volume _))).mpr
  apply (integrable_withDensity_iff_integrable_smul' (μ := volume)
    hm.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul]
  have hs := (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)
  have hw := (integrable_withDensity_iff_integrable_smul' (μ := volume)
    hm2.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hs
  simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a (k + 2) _), smul_eq_mul] at hw
  apply (hw.const_mul 2).mono' (hm.aestronglyMeasurable.mul (hmul.norm.pow 2))
  filter_upwards [] with ξ
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (homogeneousFourierWeight_nonneg a k ξ) (sq_nonneg _))]
  have hn : ‖(-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ‖ ^ 2 = ‖ξ‖ ^ 4 * ‖u ξ‖ ^ 2 := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖ξ‖), mul_pow, ← pow_mul, Nat.reduceMul]
  rw [hn]
  calc
    _ = (homogeneousFourierWeight a k ξ * ‖ξ‖ ^ 4) * ‖u ξ‖ ^ 2 := by ring
    _ ≤ (2 * homogeneousFourierWeight a (k + 2) ξ) * ‖u ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (homogeneousFourierWeight_laplacian a k ha hk ξ) (sq_nonneg _)
    _ = _ := by ring

theorem exists_homogeneous_laplacian_of_higher_order (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a (k + 2)) :
    ∃ v : HomogeneousY a k, ∀ x,
      homogeneousPhysicalCLM a k ha ha1 hk v x =
        Δ (fun y : E => homogeneousPhysicalCLM a (k + 2) ha ha1 (by linarith) u y) x := by
  let h := homogeneous_memLp_laplacian a k ha ha1 hk u
  refine ⟨h.toLp _, ?_⟩
  intro x
  have he := h.coeFn_toLp.filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  change inverseRadianFourier (h.toLp _) x = _
  rw [inverseRadianFourier_congr_ae he, laplacian_homogeneousPhysical]
  simp only [inverseRadianFourier, radianFourierIntegral, inner_neg_right, neg_neg]
  push_cast
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

end DefocusingNLS

end OAI
