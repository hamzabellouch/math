import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorProfileLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingComplexLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedInnerAmplitude
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMassConvergence

namespace OAI

/-! The actual matched profiles converge on each fixed ball, including their mass weights. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedFreeProfile (z : ProfileMatchingBall) (r : ℝ) : ℂ :=
  if r ≤ innerBoundaryRadius then
    if r ≤ radialShootingR (profileMatchingParameter z) then 1
    else (radialFreeInnerJet (profileMatchingParameter z) r).1
  else radialShootingFreeExterior z r

theorem radialMatchedProfile_uniform_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (R : ℝ) :
    TendstoUniformlyOn (fun i => radialMatchedProfile (s i) (z i))
      (radialMatchedFreeProfile z₀) atTop (Icc 0 R) := by
  have hI := (radialShootingInner_complex_C1_limit s hs
    (fun i => profileMatchingParameter (z i)) (profileMatchingParameter z₀)
    (continuous_profileMatchingParameter.continuousAt.tendsto.comp hz)).1
  have hO := radialShootingExterior_uniform_limit s hs z z₀ hz R
  rw [Metric.tendstoUniformlyOn_iff] at hI hO ⊢
  intro ε hε
  filter_upwards [hI ε hε,hO ε hε] with i hi ho r hr
  by_cases h : r ≤ innerBoundaryRadius
  · simpa only [radialMatchedFreeProfile,radialMatchedProfile,ite_eq_left h] using hi r ⟨hr.1,h⟩
  · simpa only [radialMatchedFreeProfile,radialMatchedProfile,ite_eq_right h] using
      ho r ⟨(lt_of_not_ge h).le,hr.2⟩

theorem radialMatchedFreeProfile_continuousOn (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) :
    ContinuousOn (radialMatchedFreeProfile z₀) (Icc 0 R) := by
  apply (radialMatchedProfile_uniform_limit s hs z z₀ hz R).continuousOn
  exact (Eventually.of_forall (fun i =>
    (radialMatchedProfile_differentiable (s i) (z i) (hX i) (hm i)).continuous.continuousOn)).frequently

theorem radialMatched_mass_uniform_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) :
    TendstoUniformlyOn (fun i r => ‖radialMatchedProfile (s i) (z i) r‖^2)
      (fun r => ‖radialMatchedFreeProfile z₀ r‖^2) atTop (Icc 0 R) :=
  spectralMass_uniform R _ _ (radialMatchedFreeProfile_continuousOn s hs z z₀ hz hX hm R)
    (radialMatchedProfile_uniform_limit s hs z z₀ hz R)

theorem radialMatchedFreeProfile_inner_lower (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    (999/1000 : ℝ) ≤ ‖radialMatchedFreeProfile z₀ r‖ := by
  have h := (radialMatchedProfile_uniform_limit s hs z z₀ hz innerBoundaryRadius).tendsto_at hr
  exact ge_of_tendsto (continuous_norm.continuousAt.tendsto.comp h)
    (Eventually.of_forall (fun i => (radialMatchedAmplitude_inner_bounds (s i) (z i) r hr).1.1))

theorem radialMatchedFreeProfile_ne_zero (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (r : ℝ) (hr : 0 ≤ r) :
    radialMatchedFreeProfile z₀ r ≠ 0 := by
  by_cases hi : r ≤ innerBoundaryRadius
  · exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
      (radialMatchedFreeProfile_inner_lower s hs z z₀ hz r ⟨hr,hi⟩))
  · obtain ⟨δ,ρ,hδ,_,_,_,_,hlower⟩ := radialShooting_free_annulus z₀
    rw [radialMatchedFreeProfile,ite_eq_right hi,radialShootingFreeExterior]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    exact norm_pos_iff.mp (hδ.trans (hlower (Real.log r)
      (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) (lt_of_not_ge hi).le)))

end DefocusingNLS

end OAI
