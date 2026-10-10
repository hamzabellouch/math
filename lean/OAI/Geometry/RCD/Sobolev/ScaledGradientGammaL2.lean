import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # A rescaled pointwise gradient bound gives the needed L2 mixed density -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem scaled_gradient_gamma_memLp (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) {r Q : ℝ} (hr : 0<r) (hQ0 : 0≤Q)
    (hf : ∀ᵐ x ∂μ, r^2*localGamma μ hQ f f x≤Q^2) :
    MemLp (localGamma μ hQ f g) 2 μ := by
  apply localGamma_memLp_of_bounded_gradient μ hQ f g ⟨Q/r,div_nonneg hQ0 hr.le⟩
  filter_upwards [hf,localGamma_self μ hQ f,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)] with x hx he hn
  rw [he,← mul_pow] at hx
  have hb := (sq_le_sq₀ (mul_nonneg hr.le hn) hQ0).mp hx
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hb)

end RegularPointCoordinates

end

end OAI
