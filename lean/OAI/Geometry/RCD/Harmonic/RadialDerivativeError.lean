import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation
import OAI.Geometry.RCD.Sobolev.PoissonSourceEstimates

namespace OAI

/-! # The radial derivative error from the actual Poisson energy error -/

open Set MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_sq_le (f a : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ, (localGamma μ hQ f a x) ^ 2 ≤
      localGamma μ hQ f f x * localGamma μ hQ a a x := by
  filter_upwards [localGamma_abs_le μ hQ f a,
    localGamma_self μ hQ f, localGamma_self μ hQ a] with x hcs hf ha
  have hp : 0 ≤ SobolevSpace.minimalSlope μ hQ f x * SobolevSpace.minimalSlope μ hQ a x :=
    (abs_nonneg _).trans hcs
  have hh := (sq_le_sq₀ (abs_nonneg _) hp).mpr hcs
  simpa only [sq_abs, mul_pow, hf, ha] using hh

/-- A bounded gradient in the second slot makes its pairing with every
Sobolev gradient locally square-integrable. -/
theorem localGamma_memLp_two_of_bound (Ω : Set X) (f a : SobolevSpace μ hQ)
    {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ a a x ≤ B) :
    MemLp (localGamma μ hQ f a) 2 (μ.restrict Ω) := by
  have hb : ∀ᵐ x ∂μ.restrict Ω, (localGamma μ hQ f a x) ^ 2 ≤ B * localGamma μ hQ f f x := by
    filter_upwards [ha, ae_restrict_of_ae (localGamma_sq_le μ hQ f a),
      ae_restrict_of_ae (localGamma_self μ hQ f)] with x hax hsq hself
    exact hsq.trans (by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left hax (by rw [hself]; positivity))
  have hmeas := (localGamma_memL1 μ hQ f a).aestronglyMeasurable.restrict (s := Ω)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  exact ((localGamma_memL1 μ hQ f f).integrableOn.const_mul B).mono_nonneg
    (hmeas.pow 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hb

/-- The raw radial derivative changes by at most the bounded coordinate
gradient times the Poisson energy error. -/
theorem radial_pairing_error_le (Ω : Set X) (q f a : SobolevSpace μ hQ)
    {B : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ a a x ≤ B) :
    (∫ x in Ω, (localGamma μ hQ q a x - localGamma μ hQ f a x) ^ 2 ∂μ) ≤
      B * ∫ x in Ω, localGamma μ hQ (q - f) (q - f) x ∂μ := by
  have hsq : ∀ᵐ x ∂μ.restrict Ω, (localGamma μ hQ q a x - localGamma μ hQ f a x) ^ 2 ≤
      B * localGamma μ hQ (q - f) (q - f) x := by
    filter_upwards [ae_restrict_of_ae (localGamma_sub_left μ hQ q f a),
      ae_restrict_of_ae (localGamma_sq_le μ hQ (q - f) a), ha,
      ae_restrict_of_ae (localGamma_self μ hQ (q - f))] with x hsub hcs hax hself
    rw [← hsub]
    exact hcs.trans (by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left hax (by rw [hself]; positivity))
  have hi := ((localGamma_memLp_two_of_bound μ hQ Ω q a ha).sub
    (localGamma_memLp_two_of_bound μ hQ Ω f a ha)).integrable_sq
  have hh := integral_mono_ae hi
    ((localGamma_memL1 μ hQ (q - f) (q - f)).integrableOn.const_mul B) hsq
  simpa only [integral_const_mul, Pi.sub_apply] using hh

/-- The source estimate gives a linear, not square-root, bound for the
squared radial derivative error. -/
theorem radial_pairing_error_le_source (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) (q a : SobolevSpace μ hQ)
    (H : SobolevSpace.dirichlet μ hQ Ω) (σ : Measure X) [IsFiniteMeasure σ]
    (hsource : IsDirichletMeasureSource μ hQ Ω H.val σ)
    {d C B A : ℝ} (hd : 1 < d) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hheight : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x ∧
      SobolevSpace.toLp μ hQ H.val x ≤ B)
    (ha : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ a a x ≤ A)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val) :
    (∫ x in Ω, (localGamma μ hQ q a x - localGamma μ hQ (q - H.val) a x) ^ 2 ∂μ) ≤
      A * (σ.real Ω * B) := by
  have he := (positive_source_bounds_of_measure μ hQ Ω hΩ hfin H σ hsource hd hC hB
    hheight hsob).2.2
  have hg : (∫ x in Ω, localGamma μ hQ H.val H.val x ∂μ) ≤ σ.real Ω * B := by
    rw [integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hQ H.val))]
    exact (setIntegral_le_integral
      ((localGamma_memL1 μ hQ H.val H.val).congr (localGamma_self μ hQ H.val))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).trans he
  have hh := radial_pairing_error_le μ hQ Ω q (q - H.val) a ha
  have hident : q - (q - H.val) = H.val := by abel
  rw [hident] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hg hA)

end RegularPointCoordinates

end

end OAI
