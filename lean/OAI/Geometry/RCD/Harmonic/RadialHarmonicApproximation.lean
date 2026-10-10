import OAI.Geometry.RCD.Sobolev.PoissonHessianInput
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # Harmonic approximation of the actual radial derivative -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem integral_sq_sobolev_difference (f g : SobolevSpace μ hQ) :
    (∫ x, (SobolevSpace.toLp μ hQ f x - SobolevSpace.toLp μ hQ g x) ^ 2 ∂μ) =
      ‖SobolevSpace.toLp μ hQ (f - g)‖ ^ 2 := by
  rw [map_sub, ← lp_integral_square_eq_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)] with x hx
  rw [hx]
  rfl

/-- Combining the Poisson energy error with weak cancellation constructs
a harmonic approximation to `Gamma(q,a)`. Its squared error is linear in
the two source budgets. -/
theorem LocalHessianPairing.radial_harmonic_approximation
    {Ω : Set X} (hΩ : MeasurableSet Ω) (q : SobolevSpace μ hQ)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    {c P D B error : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsSobolevHarmonicOn μ hQ Ω a) (b : ℝ)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgradient : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ a a x ≤ B)
    (hpoincare : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ φ.val‖ ^ 2 ≤ P * energyForm μ hQ φ.val φ.val)
    (hpoisson : (∫ x in Ω, localGamma μ hQ (q - f) (q - f) x ∂μ) ≤ error)
    (hhessian : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ - b * energyForm μ hQ a φ.val) ^ 2 ≤ D * energyForm μ hQ φ.val φ.val) :
    ∃ h : SobolevSpace μ hQ, G.mixed - h ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      IsSobolevHarmonicOn μ hQ Ω h ∧
      energyForm μ hQ (G.mixed - h) (G.mixed - h) ≤ 4 * D ∧
      (∫ x in Ω, (localGamma μ hQ q a x - SobolevSpace.toLp μ hQ h x) ^ 2 ∂μ) ≤
        2 * B * error + 8 * P * D := by
  obtain ⟨h, hmem, hharm, henergy, hl2⟩ :=
    G.exists_harmonic_correction μ hQ hΩ hf ha b hP hD hpoincare hhessian
  refine ⟨h, hmem, hharm, henergy, ?_⟩
  have hraw := (radial_pairing_error_le μ hQ Ω q f a hgradient).trans
    (mul_le_mul_of_nonneg_left hpoisson hB)
  have hdiffmem := (Lp.memLp (SobolevSpace.toLp μ hQ G.mixed)).sub
    (Lp.memLp (SobolevSpace.toLp μ hQ h))
  have hdiff : (∫ x in Ω,
      (SobolevSpace.toLp μ hQ G.mixed x - SobolevSpace.toLp μ hQ h x) ^ 2 ∂μ) ≤ P * (4 * D) := by
    calc
      _ ≤ ∫ x, (SobolevSpace.toLp μ hQ G.mixed x - SobolevSpace.toLp μ hQ h x) ^ 2 ∂μ :=
        setIntegral_le_integral hdiffmem.integrable_sq (Filter.Eventually.of_forall fun x => sq_nonneg _)
      _ = ‖SobolevSpace.toLp μ hQ (G.mixed - h)‖ ^ 2 := integral_sq_sobolev_difference μ hQ _ _
      _ ≤ _ := hl2
  have hrawmem := (localGamma_memLp_two_of_bound μ hQ Ω q a hgradient).sub
    ((Lp.memLp (SobolevSpace.toLp μ hQ h)).restrict Ω)
  have hpairmem := (localGamma_memLp_two_of_bound μ hQ Ω q a hgradient).sub
    (localGamma_memLp_two_of_bound μ hQ Ω f a hgradient)
  have hb : ∀ᵐ x ∂μ.restrict Ω,
      (localGamma μ hQ q a x - SobolevSpace.toLp μ hQ h x) ^ 2 ≤
        2 * (localGamma μ hQ q a x - localGamma μ hQ f a x) ^ 2 +
          2 * (SobolevSpace.toLp μ hQ G.mixed x - SobolevSpace.toLp μ hQ h x) ^ 2 := by
    filter_upwards [G.mixed_rep] with x hx
    rw [hx]
    nlinarith [sq_nonneg (localGamma μ hQ q a x - 2 * localGamma μ hQ f a x +
      SobolevSpace.toLp μ hQ h x)]
  have hi := integral_mono_ae hrawmem.integrable_sq
    ((hpairmem.integrable_sq.const_mul 2).add (hdiffmem.integrable_sq.integrableOn.const_mul 2)) hb
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  have hsplit := integral_add (hpairmem.integrable_sq.const_mul 2)
    (hdiffmem.integrable_sq.integrableOn.const_mul 2)
  simp only [Pi.sub_apply, integral_const_mul] at hsplit
  rw [hsplit] at hi
  linarith

end RegularPointCoordinates

end

end OAI
