import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSecondMomentWeight
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierPairing
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace OAI

/-! # Every actual Y vector has a classical C² physical representative -/

open MeasureTheory Filter
open scoped FourierTransform ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem integrable_homogeneousFourier_secondMoment (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) :
    Integrable (fun ξ : E => ‖ξ‖ ^ 2 * ‖u ξ‖) := by
  have hm := (continuous_homogeneousFourierWeight a k ha1 hk).measurable
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have hw : Integrable (fun ξ : E => homogeneousFourierWeight a k ξ * ‖u ξ‖ ^ 2) := by
    have hsq : Integrable (fun ξ : E => ‖u ξ‖ ^ 2) (homogeneousFourierMeasure a k) :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)
    have ht := (integrable_withDensity_iff_integrable_smul'
      hm.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hsq
    simpa only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul] using ht
  let A : E → ℝ := fun ξ => Real.sqrt (homogeneousFourierWeight a k ξ) * ‖u ξ‖
  let B : E → ℝ := fun ξ => ‖ξ‖ ^ 2 * (Real.sqrt (homogeneousFourierWeight a k ξ))⁻¹
  have hAmeas : AEStronglyMeasurable A volume := hm.sqrt.aestronglyMeasurable.mul hu.aestronglyMeasurable.norm
  have hBmeas : AEStronglyMeasurable B volume :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul hm.sqrt.inv.aestronglyMeasurable
  have hAsq (ξ : E) : A ξ ^ 2 = homogeneousFourierWeight a k ξ * ‖u ξ‖ ^ 2 := by
    simp only [A, mul_pow, Real.sq_sqrt (homogeneousFourierWeight_nonneg a k ξ)]
  have hBsq (ξ : E) : B ξ ^ 2 = ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹ := by
    simp only [B, mul_pow, inv_pow, Real.sq_sqrt (homogeneousFourierWeight_nonneg a k ξ),
      ← pow_mul, Nat.reduceMul]
  have hA : MemLp A 2 volume := (memLp_two_iff_integrable_sq hAmeas).mpr (by simpa only [hAsq] using hw)
  have hB : MemLp B 2 volume := (memLp_two_iff_integrable_sq hBmeas).mpr (by
    simpa only [hBsq] using integrable_homogeneousSecondMomentWeight a k ha ha1 hk)
  apply (hA.integrable_mul hB).congr
  have hn : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton _
  filter_upwards [hn] with ξ hξ
  have hpos := Real.sqrt_pos.mpr (homogeneousFourierWeight_pos a k ξ hξ)
  dsimp only [Pi.mul_apply, A, B]
  field_simp [ne_of_gt hpos]

theorem integrable_homogeneousFourier_moment_le_two (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (n : ℕ) (hn : n ≤ 2) : Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖u ξ‖) := by
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have h₂ := integrable_homogeneousFourier_secondMoment a k ha ha1 hk u
  apply (hu.norm.add h₂).mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul hu.aestronglyMeasurable.norm)
  filter_upwards [] with ξ
  change ‖‖ξ‖ ^ n * ‖u ξ‖‖ ≤ ‖u ξ‖ + ‖ξ‖ ^ 2 * ‖u ξ‖
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg ξ) n) (norm_nonneg (u ξ)))]
  have hp : ‖ξ‖ ^ n ≤ 1 + ‖ξ‖ ^ 2 := by
    interval_cases n
    · simp
    · simp only [pow_one]
      nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]
    · simp
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (by ring)

theorem contDiff_homogeneousPhysical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) :
    ContDiff ℝ 2 (fun x : E => homogeneousPhysicalCLM a k ha ha1 hk u x) := by
  have hF : ContDiff ℝ 2 (𝓕 (u : E → ℂ)) := by
    apply Real.contDiff_fourier
    intro n hn
    exact integrable_homogeneousFourier_moment_le_two a k ha ha1 hk u n (by exact_mod_cast hn)
  have he : (fun x : E => homogeneousPhysicalCLM a k ha ha1 hk u x) =
      (fun x : E => ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
        𝓕 (u : E → ℂ) ((2 * Real.pi)⁻¹ • (-x))) := by
    funext x
    change inverseRadianFourier (u : E → ℂ) x = _
    rw [inverseRadianFourier, radianFourierIntegral_eq_fourier]
  rw [he]
  have hs : ContDiff ℝ 2 (fun x : E => (2 * Real.pi)⁻¹ • (-x)) :=
    contDiff_const.fun_smul contDiff_id.neg
  exact contDiff_const.mul (hF.comp hs)

end DefocusingNLS

end OAI
