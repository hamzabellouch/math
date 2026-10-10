import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTransportBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeFirstBoundary

namespace OAI

/-! Uniform physical Cauchy data give the boundary bound for the actual
pressure-free gauge equation. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatched_uniform_gauge_first_boundary (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (F G f g : ℕ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r)) = (F i r,G i r))
    (hnorm : ∀ᶠ i in atTop, spectralPhysicalShellDensity (F i) (G i) R ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop,
      ‖star (f i R)*spectralGaugeSecondFlux
        (radialMatchedMassFunction (s i) (z i))
        (radialMatchedTransportFunction (s i) (z i)) (f i) (g i) R‖ ≤ L := by
  obtain ⟨c,_,hc,_,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  obtain ⟨D,_,hd⟩ := radialMatched_uniform_derivative_bound s hs z z₀ hz hX hm R hR
  obtain ⟨C,hC,hA⟩ := radialMatched_uniform_transport_bound s hs z z₀ hz hX hm R hR.le
  let K := (1+C)*(1+D^2/c)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K*M,mul_nonneg hK hM,?_⟩
  filter_upwards [hb,hd,hA,hnorm] with i hi hdi hai hni
  have hmass : radialMatchedMassFunction (s i) (z i) R=
      ‖radialMatchedEvenProfile (s i) (z i) R‖^2 := by
    rw [radialMatchedEvenProfile_nonneg (s i) (z i) R hR.le]
    rfl
  have hQi := (radialMatchedEvenProfile_contDiff (s i) (z i) (hX i) (hm i)).differentiable
    (by simp)
  have hci : c ≤ ‖radialMatchedEvenProfile (s i) (z i) R‖^2 := by
    simpa only [radialMatchedEvenProfile_nonneg (s i) (z i) R hR.le] using (hi R ⟨hR.le,le_rfl⟩).1
  have hbound := spectralGaugeSecondFlux_first_physical_energy_bound
    (radialMatchedMassFunction (s i) (z i)) (radialMatchedTransportFunction (s i) (z i))
    (radialMatchedEvenProfile (s i) (z i)) (f i) (g i) (F i) (G i) R C c D hR.le hC hc
    hci hmass (hai R ⟨hR.le,le_rfl⟩).2 hQi.differentiableAt
    ((hf i).differentiable (by norm_num)).differentiableAt
    ((hg i).differentiable (by norm_num)).differentiableAt
    (hpair i) (hdi R ⟨hR,le_rfl⟩)
  exact hbound.trans (mul_le_mul_of_nonneg_left hni hK)

end DefocusingNLS

end OAI
