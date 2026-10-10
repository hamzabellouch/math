import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FullAnnulusGeometry

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma masterWidth_relative_tendsto_half {ι : Type*} {l : Filter ι}
    {c₁ : ℝ} (hc : 0 < c₁) {r₀ s : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0)) (hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖) :
    Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i))
      l (𝓝 0) := by
  have ht : Tendsto (fun i => (c₁*200000)*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (c₁*200000)
  apply squeeze_zero' _ _ ht
  · filter_upwards [hr,hs] with i hri hsi
    exact div_nonneg (masterWidth_pos hc hri hsi _).le (by unfold localCellRadius; positivity)
  · filter_upwards [hr,hs,hry] with i hri hsi hryi
    have hyi : y i ≠ 0 := norm_pos_iff.mp (by linarith)
    have ha := localCellRadius_pos hyi
    apply (div_le_iff₀ ha).mpr
    have hh := masterWidth_upper hc.le hri hsi (y i)
    have hmax : masterBaseDistance (r₀ i) (y i) ≤ 2*‖y i‖ := by
      exact max_le (by linarith [norm_nonneg (y i)]) hryi
    calc
      _ ≤ c₁*(2*‖y i‖)*(s i)^masterExponent := hh.trans (by gcongr)
      _ = _ := by unfold localCellRadius; ring

lemma half_band_observation_width_bound {u : ℝ} {y : Space} (hu : 0 < u) (hy : u/2 ≤ ‖y‖) :
    0 ≤ u^(101/100:ℝ) ∧
      u^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius y)^(101/100:ℝ) := by
  constructor
  · positivity
  · have hh := Real.rpow_le_rpow hu.le (by linarith : u ≤ 2*‖y‖)
      (by norm_num : (0:ℝ) ≤ 101/100)
    convert hh using 1
    rw [←Real.mul_rpow (by norm_num) (by unfold localCellRadius; positivity)]
    congr 1
    unfold localCellRadius
    ring

theorem expandedAnnulus_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      LowInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      HighInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      universalCellCountConstant*(localOffsetMass (dyadicUniformEventBudget (u i) ((u i)^40) δ) (y i))^2 <
        (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c₂ : ℝ := c₁/B^(1+masterExponent)
  have hc₂ : 0 < c₂ := div_pos hc (Real.rpow_pos_of_pos hBp _)
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyl := hband.mono fun _ hi => hi.2.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hu,hyl] with i hui hyi
    exact norm_pos_iff.mp (by linarith)
  have ha := hy.mono fun _ hi => localCellRadius_pos hi
  have ha0 := fullAnnulus_local_radius_tendsto hBp.le hs0 hu hus hyu
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤
      masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hy,hu,hus,hyu] with i hyi hui husi hyui
    apply masterWidth_fullAnnulus_lower hc.le hB hyi
    exact (fullAnnulus_local_radius_le (mul_nonneg hBp.le hui.le) hyui).trans
      (mul_le_mul_of_nonneg_left husi hBp.le)
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius (y i))^(101/100:ℝ) := by
    filter_upwards [hu,hyl] with i hui hyi
    exact half_band_observation_width_bound hui hyi
  have hD := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hDgap := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num : (1/100:ℝ) < 1/10) hδ
  have hgeom := inverse_geometry_eventually ha ha0 hwidth
    (observation_relative_tendsto (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) ha ha0 hell)
  have hlow := low_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) (by linarith : 0 ≤ h) hxi
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hhigh := high_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) hxi hxih
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hcount := inverse_count_margin_eventually hy ha0 hD
  filter_upwards [hgeom,hlow,hhigh,hcount] with i hi hlo hhi hci
  refine ⟨?_,hlo,hhi,hci⟩
  rcases hi with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier

theorem own_probability_expandedAnnulus_weighted_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s p : ι → ℝ} {y : ι → Space} {B c₁ δ : ℝ} (hB : 0 ≤ B)
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      (localCellRadius (y i))^4*(p i*originalFieldCapBudget (u i) (p i) δ c₁
        (r₀ i) (s i) (y i) ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)) ≤
      (p i)^(3/4:ℝ)*(tfPatchCapConstant+1) := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp (by linarith [hi.1,hi.2.1,hi.2.2.2.1])
  have ha0 := fullAnnulus_local_radius_tendsto hB hs0 hu hus hyu
  have hD := own_probability_fullAnnulus_excess_tendsto (δ := δ) hB hu hu0 hp hp0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hlim := physical_field_cap_tendsto hy ha0 hD ht hwidth
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    tfPatchCapConstant < tfPatchCapConstant+1))
  filter_upwards [hy,hp,ht,hbound,hp0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hyi hpi hti hbi hpi1
  have ha := localCellRadius_pos hyi
  have hh := probability_weighted_cap
    (b := (localCellRadius (y i))^(6/5:ℝ))
    (q := localCellRadius (y i)*(localCellRadius (y i))^masterExponent) (D := dyadicUniformEventBudget (u i) (p i) δ)
    hyi (by positivity) (by positivity) (by positivity : 0 ≤ 2*masterWidth c₁ (r₀ i) (s i) (y i)) hpi hpi1.le
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
  change (localCellRadius (y i))^4*(p i*
    physicalFieldCapBudget (dyadicUniformEventBudget (u i) (p i) δ) (y i)
      ((localCellRadius (y i))^(6/5:ℝ))
      (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)
      (2*masterWidth c₁ (r₀ i) (s i) (y i))) ≤ _
  calc _ ≤ _ := hmul
       _ = (p i)^(3/4:ℝ)*((localCellRadius (y i))^4*
          physicalFieldCapBudget ((p i)^(1/4:ℝ)*dyadicUniformEventBudget (u i) (p i) δ) (y i)
            ((localCellRadius (y i))^(6/5:ℝ))
            (localCellRadius (y i)*(localCellRadius (y i))^masterExponent)
            (2*masterWidth c₁ (r₀ i) (s i) (y i))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hbi.le (Real.rpow_nonneg hpi.le _)

end CoulombAtom

end

end OAI
