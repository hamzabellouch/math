import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeightLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedVelocity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureSmallness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAverageUniform
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactTransform

namespace OAI

/-! The transport coefficient converges by its mass-average identity, including
the origin; no derivative convergence across the pressure layer is used. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeightedFlux_average_nonneg (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) (r : ℝ) (hr : 0 ≤ r) :
    radialWeightedFlux (radialMatchedProfile n z) r=
      (6-2*radialShootingA n)*(r*
        radialAverage (fun t => ‖radialMatchedProfile n z t‖^2) r) := by
  rcases hr.eq_or_lt with he | hp
  · subst r
    have hd := radialMatchedProfile_deriv_eq_inner n z 0
      (show 0 < innerBoundaryRadius by linarith [innerBoundaryRadius_bounds.1])
    rw [radialShootingInner_derivative_zero] at hd
    simp [radialWeightedFlux,hd]
  · simpa only [Complex.sq_norm,mul_assoc] using
      radialMatchedWeightedFlux_average n z hX hm r hp

theorem radialUniform_const_mul (R : ℝ) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hf : TendstoUniformlyOn f g atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => c n*f n r) (fun r => c₀*g r) atTop (Icc 0 R) := by
  let : CompactSpace (Icc (0 : ℝ) R) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hd : Tendsto (fun n : ℕ => (n,n)) atTop (atTop ×ˢ atTop) :=
    tendsto_id.prodMk tendsto_id
  have hp : TendstoUniformly (fun n (r : Icc (0 : ℝ) R) => (c n,f n r))
      (fun r : Icc (0 : ℝ) R => (c₀,g r)) atTop := by
    intro u hu
    exact hd.eventually ((hc.tendstoUniformly_const.prodMk
      (tendstoUniformlyOn_iff_restrict.mp hf)) u hu)
  have ht := radial_compact_transform_limit
    (fun n (r : Icc (0 : ℝ) R) => (c n,f n r))
    (fun r : Icc (0 : ℝ) R => (c₀,g r))
    (continuous_const.prodMk (hg.comp continuous_subtype_val)) hp
    (fun p : Icc (0 : ℝ) R × (ℝ × ℝ) => p.2.1*p.2.2)
    (fun _ => by fun_prop)
  exact tendstoUniformlyOn_iff_restrict.mpr ht

theorem radialMatchedWeightedFlux_uniform_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun i r => radialWeightedFlux (radialMatchedProfile (s i) (z i)) r)
      (fun r => 6*(r*radialAverage (fun t => ‖radialMatchedFreeProfile z₀ t‖^2) r))
      atTop (Icc 0 R) := by
  let f := fun i r => ‖radialMatchedProfile (s i) (z i) r‖^2
  let g := fun r => ‖radialMatchedFreeProfile z₀ r‖^2
  have hg : Continuous g := (radialMatchedFreeProfile_continuous s hs z z₀ hz hX hm).norm.pow 2
  have hf : ∀ i, ContinuousOn (f i) (Icc 0 R) := fun i =>
    ((radialMatchedProfile_differentiable (s i) (z i) (hX i) (hm i)).continuous.norm.pow 2).continuousOn
  have havg := radial_derivative_integral_uniform R hR f g hf hg.continuousOn
    (radialMatched_mass_uniform_limit s hs z z₀ hz hX hm R)
  have hc : Tendsto (fun i => 6-2*radialShootingA (s i)) atTop (𝓝 6) := by
    simpa only [Function.comp_def,mul_zero,sub_zero] using
      tendsto_const_nhds.sub ((radialShootingA_tendsto_zero.comp hs.tendsto_atTop).const_mul 2)
  have ht := radialUniform_const_mul R _ 6 hc _ _
    (continuous_id.mul (continuous_radialAverage g hg)) havg
  apply ht.congr
  exact Eventually.of_forall (fun i r hr =>
    (radialMatchedWeightedFlux_average_nonneg (s i) (z i) (hX i) (hm i) r hr.1).symm)

end DefocusingNLS

end OAI
