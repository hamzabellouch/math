import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # Mixed gradient bounds in the original physical scale -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem scaled_gamma_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) {A : Set X} {r M L : ℝ}
    (hr : 0≤r) (hM : 0≤M) (hL : 0≤L)
    (hf : ∀ᵐ x ∂μ.restrict A, r^2*localGamma μ hQ f f x≤M^2)
    (hg : ∀ᵐ x ∂μ.restrict A, r^2*localGamma μ hQ g g x≤L^2) :
    ∀ᵐ x ∂μ.restrict A, |r^2*localGamma μ hQ f g x|≤M*L := by
  filter_upwards [hf,hg,ae_restrict_of_ae (localGamma_self μ hQ f),
    ae_restrict_of_ae (localGamma_self μ hQ g),
    ae_restrict_of_ae (localGamma_abs_le μ hQ f g),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g))]
    with x hfx hgx heF heG hfg hnF hnG
  have hF : r*SobolevSpace.minimalSlope μ hQ f x≤M :=
    (sq_le_sq₀ (mul_nonneg hr hnF) hM).mp (by simpa only [mul_pow,← heF] using hfx)
  have hG : r*SobolevSpace.minimalSlope μ hQ g x≤L :=
    (sq_le_sq₀ (mul_nonneg hr hnG) hL).mp (by simpa only [mul_pow,← heG] using hgx)
  calc
    |r^2*localGamma μ hQ f g x|=r^2*|localGamma μ hQ f g x| := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
    _ ≤ r^2*(SobolevSpace.minimalSlope μ hQ f x*SobolevSpace.minimalSlope μ hQ g x) :=
      mul_le_mul_of_nonneg_left hfg (sq_nonneg r)
    _ = (r*SobolevSpace.minimalSlope μ hQ f x)*(r*SobolevSpace.minimalSlope μ hQ g x) := by ring
    _ ≤ M*L := mul_le_mul hF hG (mul_nonneg hr hnG) hM

end RegularPointCoordinates

end

end OAI
