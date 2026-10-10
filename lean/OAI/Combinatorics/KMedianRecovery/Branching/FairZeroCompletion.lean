import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.ProbabilityProd
import OAI.Combinatorics.KMedianRecovery.Recovery.ZeroObjective
import OAI.Combinatorics.KMedianRecovery.Branching.ZeroSuccessfulCompletion
import OAI.Combinatorics.KMedianRecovery.Branching.ObservableSuccessfulProbability

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]
variable {D S O : Finset V}

theorem fair_zero_completion
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (hBlue : designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50)) = ∅) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ) ≤
      probability (fun seed : (V → Fin 4) × CompletionBits F s =>
        realCost D (zeroOutput D F S hSF hS Δ hΔ hbound s
          (fun u => ColorLabel.color (seed.1 u)) q seed.2) ≤
            (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.deleted
  let dest := C.designatedDestination hD s (19/50)
  let Q := R ∪ designatedProxies R dest
  let PC : (V → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 1/(32*Real.exp (1:ℝ)) ≤ 1/16 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 32*Real.exp (1:ℝ)) (by norm_num : (0:ℝ)<16)]
    linarith
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability PC := by
    calc
      _ ≤ (1/16:ℝ)^C.bad.card := pow_le_pow_left₀ (by positivity) hbase _
      _ = (1/4:ℝ)^(2*C.bad.card) := by rw [pow_mul]; norm_num
      _ ≤ (1/4:ℝ)^Q.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ
      _ ≤ probability PC := hc
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower PC
    (fun seed bits => realCost D (zeroOutput D F S hSF hS Δ hΔ hbound s
      (fun u => ColorLabel.color (seed u)) (designatedRed R dest).card bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact C.zero_successful_probability hD Δ s hs hΔ hP hm hI hN F hSF hOF hS hbound
    (fun u => ColorLabel.color (seed u)) hseed hBlue

end MetricKMedianRecovery.Sampling.Comparison

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V] [Nonempty V]
  {D S O : Finset V}

theorem fair_color_label_completion
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (b : ℕ) (hb : 0 < b)
    (hcard : (designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card = b) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    let c := ((designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).image (C.blueDestination hD s (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ) ≤
      probability (fun seed : ((V → Fin 4) × (V → Fin (ColorLabel.labelRange b))) × CompletionBits F s =>
        realCost D (observableOutput D F S hSF hS Δ hΔ hbound s
          (fun u => ColorLabel.color (seed.1.1 u))
          (fun u => ColorLabel.label b hb (seed.1.2 u)) q c seed.2) ≤
            (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.deleted
  let dest := C.designatedDestination hD s (19/50)
  let Q := R ∪ designatedProxies R dest
  let B := designatedBlue R dest
  let PC : (V → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  let PL : (V → Fin (ColorLabel.labelRange b)) → Prop := fun seed =>
    Set.InjOn (fun i => ColorLabel.label b hb (seed i)) (↑B)
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hB : b ≤ C.bad.card := by
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hl : (1/(2*Real.exp 1))^b ≤ probability PL :=
    ColorLabel.label_event_probability B b hb hcard
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 0 ≤ 1/(2*Real.exp (1:ℝ)) := by positivity
  have hbase1 : 1/(2*Real.exp (1:ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*Real.exp (1:ℝ))]
    linarith
  have hc' : (1/4:ℝ)^(2*C.bad.card) ≤ probability PC :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ).trans hc
  have hl' : (1/(2*Real.exp 1))^C.bad.card ≤ probability PL :=
    (pow_le_pow_of_le_one hbase hbase1 hB).trans hl
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability (fun seed : (V → Fin 4) × (V → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2) := by
    rw [probability_prod_conj]
    calc
      _ = (1/4:ℝ)^(2*C.bad.card)*(1/(2*Real.exp 1))^C.bad.card := by
        rw [pow_mul,← mul_pow]
        congr 1
        ring
      _ ≤ probability PC * probability PL :=
        mul_le_mul hc' hl' (by positivity) (probability_nonneg PC)
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower
    (fun seed : (V → Fin 4) × (V → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2)
    (fun seed bits => realCost D (observableOutput D F S hSF hS Δ hΔ hbound s
      (fun u => ColorLabel.color (seed.1 u))
      (fun u => ColorLabel.label b hb (seed.2 u))
      (designatedRed R dest).card (B.image (C.blueDestination hD s (19/50))).card bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact C.observable_successful_probability hD Δ s hs hΔ hP hm hI hN F hSF hOF hS hbound
    (fun u => ColorLabel.color (seed.1 u)) hseed.1
    (fun u => ColorLabel.label b hb (seed.2 u))
    (by simpa only [Fintype.card_fin] using hcard) hseed.2

end MetricKMedianRecovery.Sampling.Comparison

end OAI
