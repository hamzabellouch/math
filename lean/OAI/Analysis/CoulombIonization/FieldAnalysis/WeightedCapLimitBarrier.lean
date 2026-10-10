import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OwnProbabilityFieldCapBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.CapProbabilityWeightBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityBudgetScaleBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

lemma physical_field_cap_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D t : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (ht : ∀ᶠ i in l, 0 ≤ t i)
    (ht0 : Tendsto (fun i => t i/localCellRadius (y i)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      physicalFieldCapBudget (D i) (y i) ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent) (2*t i))
      l (𝓝 tfPatchCapConstant) := by
  have hh := (inverse_potential_error_tendsto hy ha0 hD ht ht0).const_add tfPatchCapConstant
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hy] with i hi
  have ha := localCellRadius_pos hi
  unfold physicalFieldCapBudget
  field_simp

theorem own_probability_weighted_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s p : ι → ℝ} {y : ι → Space} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2*u i) :
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
  have hry := hband.mono fun _ hi => hi.2.1.trans hi.2.2.2.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp ((hi.1.trans_le hi.2.1).trans_le hi.2.2.2.1)
  have ha0 := band_local_radius_tendsto hs0 hu hus hyu
  have hD := own_probability_band_excess_tendsto (δ := δ) hu hu0 hp hp0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_local_relative_tendsto hc hr hs hs0 hry
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
