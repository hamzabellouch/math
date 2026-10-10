import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.SuccessfulFavorableProbability
import OAI.Combinatorics.KMedianRecovery.Branching.ObservableSuccessfulCompletion

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

theorem observable_successful_probability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s (19/50)),
      colors u = requiredColors (C.nonproxy \ s.deleted)
        (C.designatedDestination hD s (19/50)) u)
    (label : V → L)
    (hcard : (designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card = Fintype.card L)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))))) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    let c := ((designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).image (C.blueDestination hD s (19/50))).card
    (3/197:ℝ) ≤ probability (fun bits => realCost D
      (observableOutput D F S hSF hS Δ hΔ hbound s colors label q c bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) := by
  dsimp only
  apply completion_constant_success _ (comparisonCost D C.assign) hP
  · intro bits
    unfold realCost
    rw [dite_eq_left (observableOutput_feasible D F S hSF hS Δ hΔ hbound s colors label _ _ bits).2.2]
    exact Finset.sum_nonneg (fun p _ => distanceTo_nonneg _ _ _)
  · exact (C.observable_successful_completion hD Δ s hs hΔ hP hm hI hN
      F hSF hOF hS hbound colors hcolors label hcard hinj).trans
        (mul_le_mul_of_nonneg_right (by norm_num :
          (240258179/125000000:ℝ) ≤ 97/50) hP.le)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
