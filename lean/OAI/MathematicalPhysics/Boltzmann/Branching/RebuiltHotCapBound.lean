import OAI.MathematicalPhysics.Boltzmann.Branching.FamilyHotBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation

namespace OAI

section

/-! # A bounded cold family and a cap bound the full periodic solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem total_bound_of_cap {I : Type*} [Countable I] {q b L T R δ B : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) (hcap : hotPeak δ c₀ F ≤ 1)
    (hcold : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ B) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B+T+δ := by
  have hprop := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value hc₀m
    F.value_bounds hc₀ hdom (F.all_mild hT)
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F.value c₀ i u := (hprop.2.1 i u).1
  have hhot := family_hot_bounds hq hb hR hloss F.measurable_value hprop.1
    F.value_bounds hcn hprop.2.2.1
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  intro t ht
  have hratio := (hpeak t ht).trans hcap
  have hsize : PhaseEssSup.size (fun p => F.value (t,p)-
      ∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ := by
    exact (div_le_one (by linarith [ht.1] : 0 < t+δ)).mp hratio
  have hae := PhaseEssSup.ae_abs_le_size
    (hhot.1.comp (measurable_const.prodMk measurable_id))
    (fun p => show |F.value (t,p)-∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)| ≤ R from by
      rw [abs_of_nonneg (hhot.2.1 (t,p)).1]
      exact (hhot.2.1 (t,p)).2)
  filter_upwards [hcold t ht,hae] with p hp hhp
  have hh := (le_abs_self _).trans (hhp.trans hsize)
  change F.value (t,p)-(∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ at hh
  linarith [ht.2]

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # The attained cap bounds the rebuilt hot density at every time -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem hot_bound_of_cap {I : Type*} [Countable I] {q b L T R δ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) (hcap : hotPeak δ c₀ F ≤ 1) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F.value (t,p)-(∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ := by
  have hprop := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value hc₀m
    F.value_bounds hc₀ hdom (F.all_mild hT)
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F.value c₀ i u := (hprop.2.1 i u).1
  have hhot := family_hot_bounds hq hb hR hloss F.measurable_value hprop.1
    F.value_bounds hcn hprop.2.2.1
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  intro t ht
  have hsize : PhaseEssSup.size (fun p => F.value (t,p)-
      ∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ :=
    (div_le_one (by linarith [ht.1] : 0 < t+δ)).mp ((hpeak t ht).trans hcap)
  have hae := PhaseEssSup.ae_abs_le_size
    (hhot.1.comp (measurable_const.prodMk measurable_id))
    (fun p => show |F.value (t,p)-∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)| ≤ R from by
      rw [abs_of_nonneg (hhot.2.1 (t,p)).1]
      exact (hhot.2.1 (t,p)).2)
  filter_upwards [hae] with p hp
  exact (le_abs_self _).trans (hp.trans hsize)

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

end OAI
