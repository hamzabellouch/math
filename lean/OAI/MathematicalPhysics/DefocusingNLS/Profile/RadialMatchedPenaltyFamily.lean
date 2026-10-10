import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeightLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeSubunit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPressureLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPowerPressureAway
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyFamily

namespace OAI

/-! The actual matched profiles instantiate every coefficient hypothesis of the
singular pressure-inverse limit; no operator convergence is assumed here. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_penaltyFamily (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : innerBoundaryRadius ≤ R) :
    ∃ N : ℕ, ∃ F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)),
      (∀ i, (F.weight i).density=fun r => ‖radialMatchedProfile (s (i+N)) (z (i+N)) r‖^2) ∧
      F.limitWeight.density=(fun r => ‖radialMatchedFreeProfile z₀ r‖^2) ∧
      (∀ i, F.pressure i=fun r => ‖radialMatchedProfile (s (i+N)) (z (i+N)) r‖^
        (2*(s (i+N)+radialInnerShootingThreshold))) ∧
      (∀ i, F.scale i=radialShootingA (s (i+N))) ∧
      F.corePressure=radialShootingB (profileMatchingParameter z₀) := by
  obtain ⟨c,M,hc,hM,hlim,hbounds⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hbounds.and (hs.tendsto_atTop.eventually radialMatched_global_pressure_bound))
  let t := fun i => s (i+N)
  let y := fun i => z (i+N)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij N)
  have hshift : Tendsto (fun i : ℕ => i+N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i+radialInnerShootingThreshold) (y i))
      (t i+radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) := hX (i+N)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i)=0 := hm (i+N)
  let q := fun i r => ‖radialMatchedProfile (t i) (y i) r‖^2
  let q₀ := fun r => ‖radialMatchedFreeProfile z₀ r‖^2
  let p := fun i => 2*(t i+radialInnerShootingThreshold)
  let P := fun i r => ‖radialMatchedProfile (t i) (y i) r‖^(p i)
  have hq (i : ℕ) : Continuous (q i) :=
    (radialMatchedProfile_differentiable (t i) (y i) (hXt i) (hmt i)).continuous.norm.pow 2
  have hq₀ : Continuous q₀ := (radialMatchedFreeProfile_continuous s hs z z₀ hz hX hm).norm.pow 2
  have hqb (i : ℕ) : ∀ r ∈ Icc 0 R, ‖q i r‖ ≤ M :=
    fun r hr => ((hN (i+N) (by omega)).1 r hr).2
  have hql (i : ℕ) : ∀ r ∈ Icc 0 R, c ≤ q i r :=
    fun r hr => ((hN (i+N) (by omega)).1 r hr).1
  let w := fun i => spectralContinuousWeight R (q i) (hq i) M (hqb i)
  let w₀ := spectralContinuousWeight R q₀ hq₀ M (fun r hr => (hlim r hr).2)
  have hwl (i : ℕ) := spectralContinuousWeight_lower R (q i) (hq i) M (hqb i) c (hql i)
  have hw₀l := spectralContinuousWeight_lower R q₀ hq₀ M (fun r hr => (hlim r hr).2)
    c (fun r hr => (hlim r hr).1)
  have hqu := radialMatched_mass_uniform_limit t ht y z₀ hy hXt hmt R
  obtain ⟨δ,hδ,hδ0,hδb⟩ := spectralUniform_error_bound q q₀ hqu (fun i =>
    ⟨2*M,fun r hr => (norm_sub_le (q i r) (q₀ r)).trans (by
      have h1 := hqb i r hr
      have h2 := (hlim r hr).2
      linarith)⟩)
  have hp : Tendsto p atTop atTop :=
    tendsto_atTop_mono (fun i => by dsimp [p]; omega) ht.tendsto_atTop
  have hp0 (i : ℕ) : 0 < p i := by
    have h := radialShootingInner_power_pos (t i) (profileMatchingParameter (y i))
    dsimp [p]
    omega
  have hPb (i : ℕ) : ∀ r ∈ Icc 0 R, ‖P i r‖ ≤ 1 := by
    intro r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ P i r by positivity)]
    exact (hN (i+N) (by omega)).2 (y i) r hr.1
  have hPmeas (i : ℕ) : AEStronglyMeasurable (P i) (radialPressureMeasure R) :=
    ((radialMatchedProfile_differentiable (t i) (y i) (hXt i) (hmt i)).continuous.norm.pow _).aestronglyMeasurable
  have haw : ∀ d : ℝ, 0 < d → ∃ η : ℕ → ℝ, (∀ i, 0 ≤ η i) ∧
      Tendsto η atTop (𝓝 0) ∧ ∀ i, ∀ᵐ r ∂radialPressureMeasure R,
        radialShootingR (profileMatchingParameter z₀)+d < r →
          ‖(1/(p i : ℝ))⁻¹*((w i).density r*P i r)‖ ≤ η i := by
    intro d hd
    obtain ⟨ρ,hρ,hρb⟩ := radialMatchedFreeProfile_uniform_subunit t ht y z₀ hy hXt hmt R d hd
    apply spectralPower_pressure_away R (radialShootingR (profileMatchingParameter z₀)+d)
      M hM w (fun i => (w i).radial_bound)
      (fun i r => ‖radialMatchedProfile (t i) (y i) r‖)
      (fun r => ‖radialMatchedFreeProfile z₀ r‖)
      ((uniformContinuous_norm.comp_tendstoUniformlyOn
        (radialMatchedProfile_uniform_limit t ht y z₀ hy R)).mono inter_subset_left)
      ?_ (max ρ 0) (le_max_right _ _) (max_lt hρ (by norm_num)) ?_ p hp
    · intro i r hr
      rw [norm_norm]
      apply (pow_le_one_iff_of_nonneg (norm_nonneg _) (hp0 i).ne').mp
      simpa only [P,norm_pow,norm_norm] using hPb i r hr.1
    · intro r hr
      rw [norm_norm]
      exact (hρb r ⟨hr.2.le,hr.1.2⟩).trans (le_max_left _ _)
  let F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)) := {
    weight := w
    limitWeight := w₀
    lower := c
    lower_pos := hc
    radial_lower := fun i => (hwl i).1
    angular_lower := fun i => (hwl i).2
    limit_radial_lower := hw₀l.1
    limit_angular_lower := hw₀l.2
    error := δ
    error_nonneg := hδ
    error_zero := hδ0
    radial_error := fun i => radialPressureMeasure_bound R (δ i) _ (hδb i)
    angular_error := fun i => by
      unfold spectralAngularMeasure
      apply (ae_withDensity_iff (by fun_prop)).2
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
      exact hδb i r hr
    pressure := P
    pressure_measurable := hPmeas
    pressure_bound := fun i => radialPressureMeasure_bound R 1 _ (hPb i)
    pressure_nonneg := fun i => Eventually.of_forall (fun r => by positivity)
    scale := fun i => 1/(p i : ℝ)
    scale_pos := fun i => one_div_pos.mpr (Nat.cast_pos.mpr (hp0 i))
    scale_zero := (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 0)).comp hp
    corePressure := radialShootingB (profileMatchingParameter z₀)
    corePressure_pos := by have hb := (radialShooting_geometry (profileMatchingParameter z₀)).1; linarith [hb.1]
    pressure_weak := fun φ hφ => radialMatched_pressure_weakstar t ht y z₀ hy hXt hmt R hR φ hφ
    pressure_away := haw }
  refine ⟨N,F,fun _ => rfl,rfl,fun _ => rfl,?_,rfl⟩
  intro i
  dsimp [F,p,radialShootingA,t]
  push_cast
  rfl

end DefocusingNLS

end OAI
