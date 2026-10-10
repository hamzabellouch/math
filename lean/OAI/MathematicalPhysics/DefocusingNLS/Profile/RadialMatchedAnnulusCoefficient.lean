import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeSubunit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients

namespace OAI

/-! On any fixed annulus outside the limiting core, the actual nonlinear
spectral coefficients vanish uniformly as the power tends to infinity. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_annulus_coefficient_small
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (L R : ℝ) (hL : radialShootingR (profileMatchingParameter z₀)<L) :
    ∃ ε : ℕ → ℝ, (∀ i, 0 ≤ ε i) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, ∀ r ∈ Icc L R,
        ‖spectralDiagonalCoefficient (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i) r)‖+
        ‖spectralCrossCoefficient (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i) r)‖ ≤ ε i := by
  obtain ⟨ρ,hρ,hbound⟩ := radialMatchedFreeProfile_uniform_subunit s hs z z₀ hz hX hm R
    (L-radialShootingR (profileMatchingParameter z₀)) (sub_pos.mpr hL)
  let σ := max ρ (1/2)
  have hσ : σ < 1 := max_lt hρ (by norm_num)
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let τ := (σ+1)/2
  have hστ : σ < τ := by dsimp [τ]; linarith
  have hτ : τ < 1 := by dsimp [τ]; linarith
  have hτpos : 0 < τ := hσpos.trans hστ
  let m := fun i => s i+radialInnerShootingThreshold
  have hmTop : Tendsto m atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right (s i) _) hs.tendsto_atTop
  let ε := fun i => (2*(m i : ℝ)+1)*τ^(2*m i)
  refine ⟨ε,fun i => mul_nonneg (by positivity) (pow_nonneg hτpos.le _),
    (spectralSubunitCoefficient_decay τ hτpos.le hτ).comp hmTop,?_⟩
  have hclose := (Metric.tendstoUniformlyOn_iff.mp
    (radialMatchedProfile_uniform_limit s hs z z₀ hz R)) (τ-σ) (sub_pos.mpr hστ)
  filter_upwards [hclose,hmTop.eventually (eventually_ge_atTop 1)] with i hi hmi r hr
  have hr0 : r ∈ Icc 0 R :=
    ⟨(radialMatchedCore_radius_pos z₀).le.trans (hL.le.trans hr.1),hr.2⟩
  have hfree : ‖radialMatchedFreeProfile z₀ r‖ ≤ σ := by
    apply (hbound r ?_).trans (le_max_left _ _)
    simpa only [add_sub_cancel] using hr
  have hnear := hi r hr0
  have hq : ‖radialMatchedProfile (s i) (z i) r‖ ≤ τ := by
    have hn := norm_add_le (radialMatchedProfile (s i) (z i) r-radialMatchedFreeProfile z₀ r)
      (radialMatchedFreeProfile z₀ r)
    rw [sub_add_cancel] at hn
    rw [dist_comm,dist_eq_norm] at hnear
    linarith
  exact spectralCoefficient_subunit_bound (m i) hmi _ τ hq

end DefocusingNLS

end OAI
