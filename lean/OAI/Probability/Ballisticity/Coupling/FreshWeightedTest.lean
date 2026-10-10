import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma independent_random_test_weighted_lower {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (E : Set A) (hE : MeasurableSet E)
    (G : Set (A × B)) (hG : MeasurableSet G) (w : A → ℝ≥0∞) (hw : Measurable w)
    (c : ℝ≥0∞) (hbound : ∀ a ∈ E, c ≤ (μ.map V) {b | (a,b) ∈ G}) :
    c*(∫⁻ ω in U ⁻¹' E, w (U ω) ∂μ) ≤
      ∫⁻ ω in {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G}, w (U ω) ∂μ := by
  let K : Set (A × B) := (E ×ˢ Set.univ) ∩ G
  have hK : MeasurableSet K := (hE.prod MeasurableSet.univ).inter hG
  have hUV : Measurable (fun ω => (U ω,V ω)) := hU.prodMk hV
  have he : {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G} = (fun ω => (U ω,V ω)) ⁻¹' K := by
    ext ω; simp [K]
  have hf : Measurable (K.indicator (fun p : A × B => w p.1)) := (hw.comp measurable_fst).indicator hK
  have hpush : (∫⁻ ω in {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G}, w (U ω) ∂μ) =
      ∫⁻ p, K.indicator (fun q => w q.1) p ∂(μ.map U).prod (μ.map V) := by
    rw [he,←lintegral_indicator (hK.preimage hUV)]
    have heind : (fun ω => ((fun ω => (U ω,V ω)) ⁻¹' K).indicator (fun ω => w (U ω)) ω) =
        fun ω => K.indicator (fun p : A × B => w p.1) (U ω,V ω) := by
      funext ω
      by_cases h : (U ω,V ω) ∈ K <;> simp [h]
    rw [heind,←lintegral_map hf hUV,
      hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
  rw [hpush,lintegral_prod _ hf.aemeasurable]
  have hlow : (∫⁻ a, (E.indicator (fun _ => c*w a)) a ∂μ.map U) ≤
      ∫⁻ a, ∫⁻ b, K.indicator (fun p => w p.1) (a,b) ∂μ.map V ∂μ.map U := by
    apply lintegral_mono
    intro a
    dsimp only
    by_cases ha : a ∈ E
    · rw [Set.indicator_of_mem ha]
      have heq : (fun b => K.indicator (fun p => w p.1) (a,b)) =
          {b | (a,b) ∈ G}.indicator (fun _ => w a) := by
        funext b
        by_cases hb : (a,b) ∈ G <;> simp [K,ha,hb]
      have hslice : MeasurableSet {b | (a,b) ∈ G} := hG.preimage measurable_prodMk_left
      rw [heq,lintegral_indicator hslice,lintegral_const]
      simp only [Measure.restrict_apply_univ]
      calc
        c*w a ≤ (μ.map V) {b | (a,b) ∈ G}*w a := by gcongr; exact hbound a ha
        _ = w a*(μ.map V) {b | (a,b) ∈ G} := mul_comm _ _
    · rw [Set.indicator_of_notMem ha]
      exact zero_le
  refine LE.le.trans ?_ hlow
  rw [←lintegral_indicator (hE.preimage hU)]
  have heind2 : (fun ω => (U ⁻¹' E).indicator (fun ω => w (U ω)) ω) =
      fun ω => E.indicator w (U ω) := by
    funext ω
    by_cases h : U ω ∈ E <;> simp [h]
  rw [heind2,←lintegral_map (hw.indicator hE) hU]
  rw [←lintegral_const_mul c (hw.indicator hE)]
  apply le_of_eq
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ E <;> simp [ha]
end DirectionalTransience

end

end

end OAI
