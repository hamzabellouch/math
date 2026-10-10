import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.NetFieldVariationBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CapInformationBarrier
import OAI.Analysis.CoulombIonization.Localization.ObservedExpandedAnnular
import OAI.Analysis.CoulombIonization.RadialBounds.ExpandedAnnulusCapExcess

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier

 theorem actual_scaled_original_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {a c₁ δ : ℝ} (ha : 1/2 ≤ a)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ j : Fin (K i+1), (2:ℝ)^j.val*r₀ i ≤ s i →
      let u := (2:ℝ)^j.val*r₀ i
      let T := fun z => capBandStatistic (a*u) (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
      Measurable T ∧
      (physicalObservationLaw (graphRawLaw (F i)) (K i)).real {z | 1 < T z} ≤
        4096*(tfPatchCapConstant+2)*u^60 ∧
      ∀ z, T z ≤ 1 → ∀ y, 5*(a*u)/4 ≤ ‖y‖ → ‖y‖ ≤ 7*(a*u)/4 →
        (localCellRadius y)^4*
          originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y ≤
          16*(tfPatchCapConstant+3) := by
  have ha0 : 0 < a := by linarith
  have hh := actual_expandedAnnulus_cap_excess_uniform_eventually (by linarith : 1 ≤ 2*a)
    hc hcL hδ hs0 hr₀ hstate
  filter_upwards [hh,hr₀,hstate] with i hi hri hFi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hv : 0 < a*u := mul_pos ha0 hu
  have hsi : 0 < s i := hu.trans_le hjs
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  refine ⟨original_capBandStatistic_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsi _ _,?_,?_⟩
  · have hp := capBandStatistic_failure_probability
      (physicalObservationLaw (graphRawLaw (F i)) (K i)) hv
      (show 0 ≤ (tfPatchCapConstant+2)*u^60 by positivity)
      (original_capBand_excess_prod_integrable (F i) hFi.1 hFi.2.1.le (r₀ i) j hc hri hsi hv hC)
      (fun y hy => (original_smaller_cap_excess_integral (F i) (Z i) (lam i) (r₀ i) j
        hc hri hsi hv hC hy.1).trans (hi j y hjs (by nlinarith [hy.1]) (by nlinarith [hy.2])))
    simpa only [mul_assoc] using hp
  · intro z hz
    have ht := original_capBandStatistic_controls_field (F i) (Z i) (lam i) (r₀ i) j
      hc hri hsi (hru.trans hjs) z hv hC hz
    simpa only [u,add_assoc,show (2:ℝ)+1 = 3 by norm_num] using ht

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma scaled_rpow_normalization {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (D e : ℝ) :
    D*u^e = (D/a^e)*(a*u)^e := by
  rw [Real.mul_rpow ha.le hu]
  field_simp [Real.rpow_ne_zero ha.le ha.ne']

theorem exists_actual_scaled_original_regularity_constants {a c₁ : ℝ}
    (ha : 1/2 ≤ a) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ T D L A : ℝ, 0 < T ∧ 0 ≤ D ∧ 0 ≤ L ∧ 0 < A ∧
    ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let v := a*u
        let count := observedAnnularCount
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u)
        let cap := fun z => capBandStatistic v (tfPatchCapConstant+2)
          (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
        MeasurableSet[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j]
          {z | T/u^3 < count z ∨ 1 < cap z} ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/u^3 < count z ∨ 1 < cap z} ≤
            u^40+4096*(tfPatchCapConstant+2)*u^60 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i),
          count q ≤ T/u^3 → cap q ≤ 1 →
            (∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
              originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                D*v^(-6-3*masterExponent)) ∧
            (∀ y z : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v → v ≤ ‖z‖ → ‖z‖ ≤ 2*v →
              ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤
                L*v^(-7-4*masterExponent)*‖y-z‖) ∧
            (∀ y x : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 → ‖x-y‖ ≤ v^2 →
              |‖x‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q x-
                ‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y| ≤
              A*(16*(tfPatchCapConstant+3)*100000^4+D)*v^(1-3*masterExponent)+
                A*v*max (-(‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)) 0) ∧
            (∀ y : Space, 5*v/4 ≤ ‖y‖ → ‖y‖ ≤ 7*v/4 →
              (localCellRadius y)^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                16*(tfPatchCapConstant+3)) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨T,D,L,hT,hD,hL,hreg⟩ := exists_actual_expanded_conditional_regularity_constants
    (by linarith : 1 ≤ 2*a) hc hcL
  obtain ⟨A,hA,hfield⟩ := exists_original_net_field_variation_constant
  let D' := D/a^(-6-3*masterExponent)
  let L' := L/a^(-7-4*masterExponent)
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hL' : 0 ≤ L' := by dsimp [L']; positivity
  refine ⟨T,D',L',A,hT,hD',hL',hA,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have has0 : Tendsto (fun i => a*s i) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := a)).mul hs0
  filter_upwards [hreg hs0 hr₀ hstate,
    actual_scaled_original_cap_eventually ha hc hcL hδ hs0 hr₀ hstate,hr₀,
    has0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/96))]
      with i hi hcap hri hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  let v := a*u
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hv : 0 < v := mul_pos ha0 hu
  have hs : 0 < s i := hu.trans_le hjs
  have hvs : v ≤ a*s i := mul_le_mul_of_nonneg_left hjs ha0.le
  have hh := hi j hjs
  have hshape : (3:ℝ)*(2*a) = 6*a := by ring
  simp only [hshape] at hh
  have hp := (hcap j.castSucc hjs).2.1
  have hm := original_capBandStatistic_info_measurable (K := K i) (F i) (Z i) (lam i) (r₀ i) j hc hri hs
    v (tfPatchCapConstant+2)
  refine ⟨(measurableSet_lt measurable_const hh.1).union (measurableSet_lt measurable_const hm),?_,?_⟩
  · exact (measureReal_union_le _ _).trans (add_le_add hh.2.1.le hp)
  · filter_upwards [hh.2.2] with q hq
    intro hcount hcc
    obtain ⟨hden,hquery⟩ := hq hcount
    have hden' : ∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
        originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ D'*v^(-6-3*masterExponent) := by
      intro y hyl hyh
      have ht := hden y (by nlinarith) (by nlinarith)
      exact ht.trans_eq (scaled_rpow_normalization ha0 hu.le D _)
    have hquery' : ∀ y z : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v → v ≤ ‖z‖ → ‖z‖ ≤ 2*v →
        ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
          originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤ L'*v^(-7-4*masterExponent)*‖y-z‖ := by
      intro y z hyl hyh hzl hzh
      have ht := hquery y z (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
      exact ht.trans_eq (congrArg (fun t => t*‖y-z‖) (scaled_rpow_normalization ha0 hu.le L _))
    refine ⟨hden',hquery',?_,?_⟩
    · have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
      have ht := hfield (F i) (Z i) (lam i) (r₀ i) j hc hri hs (hru.trans hjs)
        q v (tfPatchCapConstant+2) D' hv (hvs.trans hsi.le) hC hD' hcc hden'
      simpa only [add_assoc,show (2:ℝ)+1 = 3 by norm_num] using ht
    · exact (hcap j.castSucc hjs).2.2 q hcc

end CoulombAtom

end

end OAI
