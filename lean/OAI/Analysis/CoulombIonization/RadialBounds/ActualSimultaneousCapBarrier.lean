import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedAnnularCountBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityRareCapBarrier
import OAI.Analysis.CoulombIonization.Ionization.SpatialCapActualBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ActualSimultaneousCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_smaller_cap_excess_integral {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    {u C : ℝ} (hu : 0 < u) (hC : 0 ≤ C) {y : Space} (hy : u ≤ ‖y‖) :
    (∫ z, max ((u/100000)^4*originalQueryField F Z lam r j c₁ r₀ s z y-C) 0
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
    (∫ z, max ((localCellRadius y)^4*originalQueryField F Z lam r j c₁ r₀ s z y-C) 0
      ∂physicalObservationLaw (graphRawLaw F) K) := by
  have hi := originalQueryField_integrable (K := K) F Z lam r j hc hr₀ hs y
  apply integral_mono_ae (((hi.const_mul _).sub (integrable_const C)).sup (integrable_const 0))
    (((hi.const_mul _).sub (integrable_const C)).sup (integrable_const 0))
  exact ae_of_all _ fun _ => scalar_cap_excess_mono (by positivity)
    (by dsimp [localCellRadius]; linarith) hC

theorem actual_simultaneous_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {c₁ δ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ j : Fin (K i+1), (2:ℝ)^j.val*r₀ i ≤ s i →
      let T := fun z => capBandStatistic ((2:ℝ)^j.val*r₀ i) (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
      Measurable T ∧
      (physicalObservationLaw (graphRawLaw (F i)) (K i)).real {z | 1 < T z} ≤
        4096*(tfPatchCapConstant+2)*((2:ℝ)^j.val*r₀ i)^60 ∧
      ∀ z, T z ≤ 1 → ∀ y, 5*((2:ℝ)^j.val*r₀ i)/4 ≤ ‖y‖ →
        ‖y‖ ≤ 7*((2:ℝ)^j.val*r₀ i)/4 →
        (localCellRadius y)^4*
          originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y ≤
          16*(tfPatchCapConstant+3) := by
  have hh := actual_cap_excess_uniform_eventually hc hcL hδ hs0 hr₀ hstate
  filter_upwards [hh,hr₀,hstate] with i hi hri hFi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hsi : 0 < s i := hu.trans_le hjs
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  refine ⟨original_capBandStatistic_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsi _ _,?_,?_⟩
  · have hp := capBandStatistic_failure_probability
      (physicalObservationLaw (graphRawLaw (F i)) (K i)) hu
      (show 0 ≤ (tfPatchCapConstant+2)*u^60 by positivity)
      (original_capBand_excess_prod_integrable (F i) hFi.1 hFi.2.1.le (r₀ i) j hc hri hsi hu hC)
      (fun y hy => (original_smaller_cap_excess_integral (F i) (Z i) (lam i) (r₀ i) j
        hc hri hsi hu hC hy.1).trans (hi j y hjs hy.1 hy.2))
    simpa only [mul_assoc] using hp
  · intro z hz
    have ht := original_capBandStatistic_controls_field (F i) (Z i) (lam i) (r₀ i) j
      hc hri hsi (hru.trans hjs) z hu hC hz
    simpa only [u,add_assoc,show (2:ℝ)+1 = 3 by norm_num] using ht

end Work_ActualSimultaneousCap_barrier_scope

section Work_AnnularMomentMonotone_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombBarrier

lemma rawAnnularCount_mono {N : ℕ} {a b A B : ℝ} (ha : A ≤ a) (hb : b ≤ B)
    (x : Configuration N) : rawAnnularCount a b x ≤ rawAnnularCount A B x := by
  unfold rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · exact False.elim (hj ⟨ha.trans hi.1,hi.2.trans hb⟩)
  · norm_num
  · exact le_rfl

lemma rawAnnularMoment_mono {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {a b A B : ℝ} (ha : A ≤ a) (hb : b ≤ B) :
    rawAnnularMoment ψ a b ≤ rawAnnularMoment ψ A B := by
  let := formRawLaw_finite hψ
  rw [rawAnnularMoment_eq_integral hψ,rawAnnularMoment_eq_integral hψ]
  exact integral_mono (rawAnnularCount_sq_integrable _ _ _) (rawAnnularCount_sq_integrable _ _ _)
    (fun x => pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ x) (rawAnnularCount_mono ha hb x) 2)

end Work_AnnularMomentMonotone_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem exists_tail_state_annular_count_constant {alpha beta : ℝ} (ha : 0 < alpha) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z lam r : ℝ}, 0 ≤ Z → 0 < lam → 0 < r →
      ∀ {N K : ℕ} {F : fermionGraph N} {p₀ : Fin (K+1) → ℝ} {δ : ℝ},
      TailTiltState Z lam r K p₀ δ F →
      ∀ (j : Fin (K+1)) (k : Fin K), j.val ≤ k.val →
      ∀ (u T : ℝ), 0 < u → 0 ≤ T →
      Real.sqrt 3*dyadicObservationWidth r k ≤ alpha*u/2 →
      Real.sqrt 3*dyadicObservationWidth r k ≤ beta*u →
      C*(annularOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) u)^2 < T^2 →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | T < observedAnnularCount (fun k : Fin K => dyadicObservationWidth r k) k
          (alpha*u) (beta*u) z}).toReal < p₀ j := by
  obtain ⟨C,hC,hbound⟩ := exists_priced_annular_count_constant (beta := 2*beta) (by linarith : 0 < alpha/2)
  refine ⟨C,hC,?_⟩
  intro Z lam r hZ hlam hr N K F p₀ δ hstate j k hk u T hu hT hnoiseA hnoiseB hlarge
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) := {z | T < observedAnnularCount ell k (alpha*u) (beta*u) z}
  have hA : MeasurableSet[observationInformation ell j] A := measurableSet_lt measurable_const
    (observedAnnularCount_information_measurable ell k hk _ _)
  by_contra! hn
  obtain ⟨G,hGn,hlaw,hD⟩ := hstate.2.2 j A hA hn
  have hlower := event_raw_annular_count_lower F G hGn ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k (alpha*u) (beta*u) hT ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hlaw
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have hmoment := rawAnnularMoment_mono hψ.sobolevFermion.sobolevVector
    (by dsimp only [ell]; linarith : alpha/2*u ≤ alpha*u-Real.sqrt 3*ell k)
    (by dsimp only [ell]; linarith : beta*u+Real.sqrt 3*ell k ≤ (2*beta)*u)
  have hD0 := le_trans (le_max_right (corePriceExcess Z lam (graphFormVector G)) 0) hD
  have hupper := hbound Z lam N (graphFormVector G) hψ.sobolevFermion hm hZ hlam
    (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) u hD0 hu hD
  exact (not_le_of_gt hlarge) (hlower.trans (hmoment.trans hupper))

end CoulombAtom

end

end OAI
