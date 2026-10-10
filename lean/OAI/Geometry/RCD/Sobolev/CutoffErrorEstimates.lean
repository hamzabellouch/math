import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff
import OAI.Geometry.RCD.Heat.HarmonicBochnerHeatSource

namespace OAI

/-! # Annular support and heat bounds for the cutoff error -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The product-rule error lives only in the transition annulus. -/
theorem GoodLaplacianCutoff.error_zero_off_annulus {p : X} {r C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p r C) (g : SobolevSpace μ hQ) :
    ∀ᵐ z ∂μ, z ∉ {z | r ≤ dist p z ∧ dist p z ≤ 2 * r} →
      cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian z = 0 := by
  filter_upwards [χ.representative, χ.laplacian_locality,
    localGamma_zero_on_level μ hQ χ.sobolev g 0,
    localGamma_zero_on_level μ hQ χ.sobolev g 1,
    localGamma_comm μ hQ g χ.sobolev] with z hz hq h0 h1 hc hnot
  by_cases hin : dist p z < r
  · have he : SobolevSpace.toLp μ hQ χ.sobolev z = 1 :=
      hz.trans (χ.one z (by simpa only [mem_ball, dist_comm] using hin))
    simp only [cutoffSourceDensity, hq (Or.inl hin), hc, h1 he, mul_zero, add_zero]
  · have hout : 2 * r < dist p z := by
      have hlow : r ≤ dist p z := le_of_not_gt hin
      by_contra hh
      exact hnot ⟨hlow, le_of_not_gt hh⟩
    have he : SobolevSpace.toLp μ hQ χ.sobolev z = 0 := hz.trans (χ.zero z hout)
    simp only [cutoffSourceDensity, hq (Or.inr hout), hc, h0 he, mul_zero, add_zero]

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
/-- A kernel bound is needed only where the integrable error is supported. -/
theorem abs_integral_mul_le_of_bound_on {f k : X → ℝ} (hf : Integrable f μ)
    {S : Set X} {A : ℝ} (_hA : 0 ≤ A)
    (hzero : ∀ᵐ z ∂μ, z ∉ S → f z = 0) (hk : ∀ z ∈ S, |k z| ≤ A) :
    |∫ z, k z * f z ∂μ| ≤ A * ∫ z, |f z| ∂μ := by
  have hb : ∀ᵐ z ∂μ, ‖k z * f z‖ ≤ A * |f z| := by
    filter_upwards [hzero] with z hz
    by_cases hin : z ∈ S
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hk z hin) (abs_nonneg _)
    · simp only [hz hin, mul_zero, norm_zero, abs_zero, le_refl]
  have hh := norm_integral_le_of_norm_le (hf.abs.const_mul A) hb
  simpa only [Real.norm_eq_abs, integral_const_mul] using hh

/-- The cutoff error is controlled by a heat-kernel estimate on its
annulus and its finite L1 mass. -/
theorem GoodLaplacianCutoff.heat_error_le {p : X} {r C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p r C) (g : SobolevSpace μ hQ)
    (k : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hk : ∀ z, r ≤ dist p z → dist p z ≤ 2 * r → |k z| ≤ A) :
    |∫ z, k z * cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian z ∂μ| ≤
      A * ∫ z, |cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian z| ∂μ :=
  abs_integral_mul_le_of_bound_on μ (cutoffSourceDensity_integrable μ hQ g χ.sobolev χ.laplacian)
    hA (χ.error_zero_off_annulus μ hQ g) (fun z hz => hk z hz.1 hz.2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
  [μ.Regular] {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)

/-- Unit heat mass and the local gradient bound give a uniform upper
bound on the actual cutoff Gram, at every positive time. -/
theorem LocalHarmonicEnergy.heatGram_le
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    {t : ℝ} (ht : 0 < t) (x : X) :
    ⟪v, cutoffHeatGram μ hQ hk χ.continuous hχs U ht x 0 v⟫_ℝ ≤
      (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  let B : ℝ := (L : ℝ) ^ 2 * ‖v‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hbound : ∀ᵐ z ∂μ,
      χ z * (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2 ≤ B := by
    filter_upwards [G.bounded, (ae_restrict_iff' measurableSet_ball).mp G.representative,
      localGamma_self μ hQ (U v)] with z hb hz hΓ
    by_cases hin : z ∈ ball p (2 * r)
    · have hg : (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2 ≤ B := by
        rw [hz hin, hΓ] at hb
        have hb' : |(SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2| ≤ B := by
          simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, B] using hb
        exact (le_abs_self _).trans hb'
      exact (mul_le_mul_of_nonneg_right (hχ z).2 (sq_nonneg _)).trans (by simpa using hg)
    · have hzero : χ z = 0 := by
        by_contra hh
        exact hin (hχΩ (subset_closure hh))
      simpa only [hzero, zero_mul] using hB
  have hi : Integrable (fun z => (χ z * k t x z) *
      (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2) μ :=
    ((Lp.memLp _).integrable_sq).bdd_mul
      (χ.continuous.mul (hk.continuous_right t ht x)).aestronglyMeasurable
      (Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hk χ.continuous hχs ht x))
  rw [cutoffHeatGram_energy]
  simp only [zero_mul, add_zero]
  calc
    _ ≤ ∫ z, k t x z * B ∂μ := by
      apply integral_mono_ae hi ((hk.integrable t ht x).mul_const B)
      filter_upwards [hbound] with z hz
      nlinarith [hk.nonneg t ht x z]
    _ = B := by rw [integral_mul_const, hk.mass_one t ht x, one_mul]

end RegularPointCoordinates

end

end OAI
