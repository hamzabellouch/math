import OAI.Geometry.RCD.Sobolev.GammaSquareDifference

namespace OAI

/-! # Local rescaled energy densities inherit the strong gradient error -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem local_scaled_gamma_difference_sq_le (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {Ω : Set X} {r M Q : ℝ} (hr : 0<r) (hM : 0≤M) (hQ0 : 0≤Q)
    (f g : SobolevSpace μ hQ)
    (hf : ∀ᵐ x ∂μ.restrict Ω, r^2*localGamma μ hQ f f x≤M^2)
    (hg : ∀ᵐ x ∂μ.restrict Ω, r^2*localGamma μ hQ g g x≤Q^2) :
    ∀ᵐ x ∂μ.restrict Ω,
      (r^2*(localGamma μ hQ f f x-localGamma μ hQ g g x))^2≤
        (M+Q)^2*(r^2*localGamma μ hQ (f-g) (f-g) x) := by
  filter_upwards [hf,hg,
    ae_restrict_of_ae (localGamma_self μ hQ f),ae_restrict_of_ae (localGamma_self μ hQ g),
    ae_restrict_of_ae (localGamma_self μ hQ (f-g)),
    ae_restrict_of_ae (localGamma_sub_left μ hQ f g f),
    ae_restrict_of_ae (localGamma_sub_left μ hQ f g g),
    ae_restrict_of_ae (localGamma_comm μ hQ f g),
    ae_restrict_of_ae (localGamma_abs_le μ hQ (f-g) f),
    ae_restrict_of_ae (localGamma_abs_le μ hQ (f-g) g),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (f-g)))]
    with x hfx hgx hsf hsg hsd hdf hdg hfg hadf hadg hnf hng hnd
  have hfm : r*SobolevSpace.minimalSlope μ hQ f x≤M := by
    apply (sq_le_sq₀ (mul_nonneg hr.le hnf) hM).mp
    rw [mul_pow,← hsf]
    exact hfx
  have hgm : r*SobolevSpace.minimalSlope μ hQ g x≤Q := by
    apply (sq_le_sq₀ (mul_nonneg hr.le hng) hQ0).mp
    rw [mul_pow,← hsg]
    exact hgx
  have he : localGamma μ hQ f f x-localGamma μ hQ g g x=
      localGamma μ hQ (f-g) f x+localGamma μ hQ (f-g) g x := by
    rw [hdf,hdg,hfg]
    ring
  have ha : |r^2*(localGamma μ hQ f f x-localGamma μ hQ g g x)|≤
      (M+Q)*(r*SobolevSpace.minimalSlope μ hQ (f-g) x) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _),he]
    calc _ ≤ r^2*(|localGamma μ hQ (f-g) f x|+|localGamma μ hQ (f-g) g x|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (sq_nonneg _)
         _ ≤ r^2*(SobolevSpace.minimalSlope μ hQ (f-g) x*SobolevSpace.minimalSlope μ hQ f x+
              SobolevSpace.minimalSlope μ hQ (f-g) x*SobolevSpace.minimalSlope μ hQ g x) :=
            mul_le_mul_of_nonneg_left (add_le_add hadf hadg) (sq_nonneg _)
         _ = (r*SobolevSpace.minimalSlope μ hQ f x+r*SobolevSpace.minimalSlope μ hQ g x)*
              (r*SobolevSpace.minimalSlope μ hQ (f-g) x) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add hfm hgm) (mul_nonneg hr.le hnd)
  have hp := pow_le_pow_left₀ (abs_nonneg _) ha 2
  simpa only [sq_abs,mul_pow,hsd] using hp

end RegularPointCoordinates

end

end OAI
