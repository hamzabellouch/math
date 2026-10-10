import OAI.Geometry.RCD.Metric.PositiveSourceMeasure

namespace OAI

/-!
# Energy-density error for a Poisson replacement

The linear positive-source gradient bound controls the difference of the
squared gradients of the boundary datum and its Poisson replacement. This is
the error paired with the Laplacian of a cutoff in the shifted Bochner mass.
-/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Pointwise polarization with the actual minimal weak upper gradient. -/
theorem poisson_energy_density_error_ae (q h : SobolevSpace μ hQ) :
    ∀ᵐ x ∂μ,
      |(1 / 2 : ℝ) * localGamma μ hQ (q - h) (q - h) x -
        (1 / 2 : ℝ) * localGamma μ hQ q q x| ≤
      SobolevSpace.minimalSlope μ hQ q x * SobolevSpace.minimalSlope μ hQ h x +
        (1 / 2 : ℝ) * (SobolevSpace.minimalSlope μ hQ h x) ^ 2 := by
  filter_upwards [localGamma_sub_left μ hQ q h (q - h),
    localGamma_comm μ hQ q (q - h), localGamma_comm μ hQ h (q - h),
    localGamma_sub_left μ hQ q h q, localGamma_sub_left μ hQ q h h,
    localGamma_comm μ hQ h q, localGamma_self μ hQ h,
    localGamma_abs_le μ hQ q h] with x hs hc hd hs' ht hcomm hself hcs
  have hid : (1 / 2 : ℝ) * localGamma μ hQ (q - h) (q - h) x -
      (1 / 2 : ℝ) * localGamma μ hQ q q x =
      -localGamma μ hQ q h x + (1 / 2 : ℝ) * (SobolevSpace.minimalSlope μ hQ h x) ^ 2 := by
    rw [hs, hc, hd, hs', ht, hcomm, hself]
    ring
  rw [hid]
  calc
    _ ≤ |-localGamma μ hQ q h x| +
        |(1 / 2 : ℝ) * (SobolevSpace.minimalSlope μ hQ h x) ^ 2| := abs_add_le _ _
    _ = |localGamma μ hQ q h x| +
        (1 / 2 : ℝ) * (SobolevSpace.minimalSlope μ hQ h x) ^ 2 := by
      rw [abs_neg, abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) *
        (SobolevSpace.minimalSlope μ hQ h x) ^ 2 from
          mul_nonneg (by norm_num) (sq_nonneg _))]
    _ ≤ _ := add_le_add hcs le_rfl

/-- Integral form of the energy-density error. -/
theorem poisson_energy_density_error_le (Ω : Set X) (q h : SobolevSpace μ hQ)
    {A : ℝ}
    (hq : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ hQ q x ≤ A)
    (hhi : IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ h x) Ω μ) :
    (∫ x in Ω, |(1 / 2 : ℝ) * localGamma μ hQ (q - h) (q - h) x -
      (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ) ≤
      A * (∫ x in Ω, SobolevSpace.minimalSlope μ hQ h x ∂μ) +
        (1 / 2 : ℝ) * ∫ x in Ω, (SobolevSpace.minimalSlope μ hQ h x) ^ 2 ∂μ := by
  have hsq : IntegrableOn (fun x => (SobolevSpace.minimalSlope μ hQ h x) ^ 2) Ω μ :=
    ((localGamma_memL1 μ hQ h h).congr (localGamma_self μ hQ h)).integrableOn
  have herr := (((localGamma_memL1 μ hQ (q - h) (q - h)).const_mul (1 / 2 : ℝ)).sub
    ((localGamma_memL1 μ hQ q q).const_mul (1 / 2 : ℝ))).abs.integrableOn (s := Ω)
  have hb : ∀ᵐ x ∂μ.restrict Ω,
      |(1 / 2 : ℝ) * localGamma μ hQ (q - h) (q - h) x -
        (1 / 2 : ℝ) * localGamma μ hQ q q x| ≤
      A * SobolevSpace.minimalSlope μ hQ h x +
        (1 / 2 : ℝ) * (SobolevSpace.minimalSlope μ hQ h x) ^ 2 := by
    filter_upwards [ae_restrict_of_ae (poisson_energy_density_error_ae μ hQ q h), hq,
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ h))]
      with x he hq hg
    exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hq hg) le_rfl)
  have hi := integral_mono_ae herr ((hhi.const_mul A).add (hsq.const_mul (1 / 2 : ℝ))) hb
  simpa only [Pi.add_apply, Pi.sub_apply, integral_add (hhi.const_mul A) (hsq.const_mul (1 / 2 : ℝ)), integral_const_mul] using hi

/-- Linear source-mass control of the replacement's energy-density error. -/
theorem poisson_energy_density_error_le_source (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hΩfin : μ Ω ≠ ∞) (q : SobolevSpace μ hQ) (h : SobolevSpace.dirichlet μ hQ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hsource : IsDirichletMeasureSource μ hQ Ω h.val σ)
    {d C B A : ℝ} (hd : 1 < d) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hh : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ h.val x ∧
      SobolevSpace.toLp μ hQ h.val x ≤ B)
    (hq : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ hQ q x ≤ A)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val) :
    (∫ x in Ω, |(1 / 2 : ℝ) * localGamma μ hQ (q - h.val) (q - h.val) x -
      (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ) ≤
      (A * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2) + B / 2) * σ.real Ω := by
  obtain ⟨hi, hL1, hL2⟩ := positive_source_bounds_of_measure μ hQ Ω hΩ hΩfin h σ
    hsource hd hC hB hh hsob
  have hsq : Integrable (fun x => (SobolevSpace.minimalSlope μ hQ h.val x) ^ 2) μ :=
    (localGamma_memL1 μ hQ h.val h.val).congr (localGamma_self μ hQ h.val)
  have hL2' : (∫ x in Ω, (SobolevSpace.minimalSlope μ hQ h.val x) ^ 2 ∂μ) ≤ σ.real Ω * B := by
    exact (setIntegral_le_integral hsq (Filter.Eventually.of_forall fun _ => sq_nonneg _)).trans hL2
  calc
    _ ≤ A * (∫ x in Ω, SobolevSpace.minimalSlope μ hQ h.val x ∂μ) +
        (1 / 2 : ℝ) * ∫ x in Ω, (SobolevSpace.minimalSlope μ hQ h.val x) ^ 2 ∂μ :=
      poisson_energy_density_error_le μ hQ Ω q h.val hq hi
    _ ≤ A * (σ.real Ω * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2)) +
        (1 / 2 : ℝ) * (σ.real Ω * B) :=
      add_le_add (mul_le_mul_of_nonneg_left hL1 hA) (mul_le_mul_of_nonneg_left hL2' (by norm_num))
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
