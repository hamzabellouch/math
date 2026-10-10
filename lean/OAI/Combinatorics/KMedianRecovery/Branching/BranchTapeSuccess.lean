import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalIndex
import OAI.Combinatorics.KMedianRecovery.Branching.FairZeroCompletion

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma branchTape_success
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) :
    ∃ b q c : Fin (C.bad.card+1), ∃ hs' : s.leaves.length ≤ C.bad.card,
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ) ≤
      probability (fun tape : Fin (localTapeBound F C.bad.card) → Bool =>
        realCost D (branchTapeOutput D F S hSF hS Δ hΔ hbound s C.bad.card b q c hs'
          (Nat.le_of_lt_succ b.isLt) tape) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  let : Nonempty V := ⟨hS.choose⟩
  let R := C.nonproxy \ s.deleted
  let dest := C.designatedDestination hD s (19/50)
  let B := designatedBlue R dest
  let q := (designatedRed R dest).card
  let c := (B.image (C.blueDestination hD s (19/50))).card
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hB : B.card ≤ C.bad.card := (Finset.card_filter_le _ _).trans hR
  have hq : q ≤ C.bad.card := (Finset.card_filter_le _ _).trans hR
  have hc : c ≤ C.bad.card := (Finset.card_image_le).trans hB
  refine ⟨⟨B.card,Nat.lt_succ_of_le hB⟩,⟨q,Nat.lt_succ_of_le hq⟩,
    ⟨c,Nat.lt_succ_of_le hc⟩,(C.correct_lengths hD _ s hs).1,?_⟩
  rw [branchTape_probability]
  by_cases hb : 0 < B.card
  · have hh := C.fair_color_label_completion hD Δ s hs hΔ hP hm hI hN
      F hSF hOF hS hbound B.card hb rfl
    simpa only [branchJointOutput,dite_eq_left hb] using hh
  · have hB0 : B = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hb)
    let : Nonempty (V → Fin (ColorLabel.labelRange B.card)) :=
      ⟨fun _ => ⟨0,by unfold ColorLabel.labelRange; positivity⟩⟩
    have hh := C.fair_zero_completion hD Δ s hs hΔ hP hm hI hN
      F hSF hOF hS hbound hB0
    simp only [branchJointOutput,dite_eq_right hb]
    have he := probability_ignore_middle (Ξ := V → Fin (ColorLabel.labelRange B.card))
      (fun (colors : V → Fin 4) (bits : CompletionBits F s) =>
        realCost D (zeroOutput D F S hSF hS Δ hΔ hbound s
          (fun u => ColorLabel.color (colors u)) q bits) ≤ (197/100:ℝ)*comparisonCost D C.assign)
    exact hh.trans_eq he.symm
end MetricKMedianRecovery.Sampling.Comparison

end OAI
