import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.InverseNumericalStatementsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BandInverseNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

structure InverseFiniteGeometry (c₁ r₀ s ell : ℝ) (y : Space) : Prop where
  radius_le : localCellRadius y ≤ 1
  cut_pos : 0 < (localCellRadius y)^(6/5:ℝ)
  cut_le : 2*(localCellRadius y)^(6/5:ℝ) ≤ localCellRadius y
  probe_pos : 0 < localCellRadius y*(localCellRadius y)^masterExponent
  probe_fit : localCellRadius y*(localCellRadius y)^masterExponent+
    Real.sqrt 3*(localCellRadius y)^(6/5:ℝ) ≤ 4*localCellRadius y
  probe_margin : localCellRadius y*(localCellRadius y)^masterExponent ≤
    3*(5*localCellRadius y-4*(localCellRadius y)^(6/5:ℝ))/4
  collar : localCellRadius y ≤ ((localCellRadius y)^(6/5:ℝ))^2*(1/(localCellRadius y)^3)
  master_fit : 3*masterWidth c₁ r₀ s y ≤
    (5*localCellRadius y-4*(localCellRadius y)^(6/5:ℝ))/12
  count_fit : 2*masterWidth c₁ r₀ s y+
    Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+2*ell) < localCellRadius y

 def quantumInverseCountConstant : ℝ := 2*universalCellCountConstant+1

lemma quantumInverseCountConstant_pos : 0 < quantumInverseCountConstant := by
  have := universalCellCountConstant_one_le
  unfold quantumInverseCountConstant
  linarith

lemma quantumInverseCountConstant_square : universalCellCountConstant < quantumInverseCountConstant^2 := by
  have := universalCellCountConstant_one_le
  unfold quantumInverseCountConstant
  nlinarith [sq_nonneg universalCellCountConstant]

lemma inverse_count_margin_eventually {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0)) :
    ∀ᶠ i in l, universalCellCountConstant*(localOffsetMass (D i) (y i))^2 <
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hm := physical_local_mass_tendsto hy ha0 masterExponent_pos hD
  have hh := ((hm.pow 2).const_mul universalCellCountConstant).eventually_lt
    (tendsto_const_nhds (x := quantumInverseCountConstant^2))
    (by simpa using quantumInverseCountConstant_square)
  filter_upwards [hy,hh] with i hyi hi
  have ha := localCellRadius_pos hyi
  have hscale : (localCellRadius (y i))^6*
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 = quantumInverseCountConstant^2 := by
    field_simp
  apply (mul_lt_mul_iff_right₀ (pow_pos ha 6)).mp
  rw [hscale]
  nlinarith only [hi]

theorem band_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {c₁ h xi δ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      LowInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      HighInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      universalCellCountConstant*(localOffsetMass (dyadicUniformEventBudget (u i) ((u i)^40) δ) (y i))^2 <
        (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyl := hband.mono fun _ hi => hi.2.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry := hband.mono fun _ hi => hi.2.1.trans hi.2.2.2.1
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hu,hyl] with i hui hyi
    exact norm_pos_iff.mp (hui.trans_le hyi)
  have ha := hy.mono fun _ hi => localCellRadius_pos hi
  have ha0 := band_local_radius_tendsto hs0 hu hus hyu
  have hwidth := masterWidth_local_relative_tendsto hc hr hs hs0 hry
  have hw : ∀ᶠ i in l, c₁*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [ha,hu,hus,hyu] with i hai hui husi hyui
    apply masterWidth_radius_lower hc.le hai ((band_local_radius_le hui.le hyui).trans husi)
    unfold localCellRadius
    linarith [norm_nonneg (y i)]
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ (100000:ℝ)^(101/100:ℝ)*(localCellRadius (y i))^(101/100:ℝ) := by
    filter_upwards [hu,hyl] with i hui hyi
    exact band_observation_width_bound hui hyi
  have hD := band_event_excess_tendsto (δ := δ) hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hDgap := band_event_excess_tendsto (δ := δ) hu hu0 hyu (by norm_num : (1/100:ℝ) < 1/10) hδ
  have hgeom := inverse_geometry_eventually ha ha0 hwidth
    (observation_relative_tendsto (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) ha ha0 hell)
  have hlow := low_inverse_numerics_eventually (C := quantumInverseCountConstant) hc hcL
    (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) (by linarith : 0 ≤ h) hxi
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hhigh := high_inverse_numerics_eventually (C := quantumInverseCountConstant) hc hcL
    (by positivity : 0 ≤ (100000:ℝ)^(101/100:ℝ)) hxi hxih
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hcount := inverse_count_margin_eventually hy ha0 hD
  filter_upwards [hgeom,hlow,hhigh,hcount] with i hi hlo hhi hci
  refine ⟨?_,hlo,hhi,hci⟩
  rcases hi with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end Work_BandInverseNumerics_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.local_count_failure {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (hstate : TailTiltState Z lam r K p₀ δ F)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (R T : ℝ) (hT : 0 ≤ T)
    (hRQ : R+Real.sqrt 3*dyadicObservationWidth r k < localCellRadius y)
    (hlarge : universalCellCountConstant*
      (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)^2 < T^2) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | T < observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y R z}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) := {z | T < observedLocalCount ell k y R z}
  have hA : MeasurableSet[observationInformation ell j] A := measurableSet_lt measurable_const
    (observedLocalCount_information_measurable ell k hk y R)
  by_contra! hn
  obtain ⟨G,hGn,hlaw,hD⟩ := hstate.2.2 j A hA hn
  have hlower := event_raw_count_lower F G hGn ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k y hT hRQ ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hlaw
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have hupper := priced_local_cell_count hψ.sobolevFermion hm hZ hlam hy
  have he := pow_le_pow_left₀
    (le_trans zero_le_one (localOffsetMass_one_le (max (corePriceExcess Z lam (graphFormVector G)) 0) y))
    (localOffsetMass_mono hD y) 2
  have hbound := hupper.trans (mul_le_mul_of_nonneg_left he
    (le_trans zero_le_one universalCellCountConstant_one_le))
  exact (not_le_of_gt hlarge) (hlower.trans hbound)

end CoulombAtom

end

end OAI
