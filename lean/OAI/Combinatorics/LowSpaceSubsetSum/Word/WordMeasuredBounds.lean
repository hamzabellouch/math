import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordMeasuredDecision
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordActionBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordExecutionAsymptotics

namespace OAI

/-! # All-execution bounds including word sampling and retained seeds -/

noncomputable section
namespace LowSpaceSubsetSum.WordMeasuredBounds

open WordSeedMeasured

variable {n : ℕ}

private theorem add_work (u H k W : ℕ) (hu : 3 ≤ u) (hH : 1 ≤ H)
    (hk : 1 ≤ k) (hW : W ≤ 2*(u^k*H)+3) : W ≤ u^(k+1)*H := by
  have hp : u ≤ u^k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) hk
  have hm : u^k ≤ u^k*H := Nat.le_mul_of_pos_right _ hH
  calc
    W ≤ 3*(u^k*H) := by omega
    _ ≤ u*(u^k*H) := Nat.mul_le_mul_right _ hu
    _ = _ := by rw [←Nat.mul_assoc,←pow_succ']

private theorem add_work_input (A B : ℕ) (h : A ≤ B) :
    A+B+1 ≤ 2*B+3 := by omega

private theorem sampled {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} {X : WordSeedRealization.Realization w N S}
    (I : Instance n) (hn : 10000 ≤ n) (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (hE : E.Bounded (inputScale I^11*2^((n+1)/2))
      (inputScale I^11*(compressionDictionaryCapacity n+1))
      (inputScale I^11*(compressionDictionaryCapacity n+1)))
    (k : ℕ) (hk : 11 ≤ k)
    (hW : ∀ s, (action s).1.2 ≤ inputScale I^k*2^((n+1)/2))
    (hD : ∀ s, (action s).2 ≤ 36*inputScale I^14*(compressionDictionaryCapacity n+1))
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (WordSampledAction.run E action stream cursor).work ≤ inputScale I^(k+1)*2^((n+1)/2) ∧
    (WordSampledAction.run E action stream cursor).cells ≤
      38*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  have h := WordSampledAction.bounded E action _ _ _ _ _ hE hW hD stream cursor
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp := Nat.mul_le_mul_right (2^((n+1)/2))
    (Nat.pow_le_pow_right (n := inputScale I) (by omega) hk)
  have hsum := h.1.trans (add_work_input
    (inputScale I^11*2^((n+1)/2)) (inputScale I^k*2^((n+1)/2)) hp)
  have hw := add_work (inputScale I) (2^((n+1)/2)) k _
    (by omega) Nat.one_le_two_pow (by omega) hsum
  refine ⟨hw,h.2.trans ?_⟩
  have hm := Nat.mul_le_mul_right (compressionDictionaryCapacity n+1)
    (Nat.pow_le_pow_right (n := inputScale I) (by omega) (by decide : 11 ≤ 14))
  have hl : 8 ≤ inputScale I^14*(compressionDictionaryCapacity n+1) := by
    have hp : inputScale I ≤ inputScale I^14 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < inputScale I) (by decide : 1 ≤ 14)
    exact (show 8 ≤ inputScale I by omega).trans (hp.trans (Nat.le_mul_of_pos_right _ (by omega)))
  rw [Nat.mul_assoc 36, Nat.mul_assoc 38]
  apply max_le <;> omega

private theorem sampled_501 {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} {X : WordSeedRealization.Realization w N S}
    (I : Instance n) (hn : 10000 ≤ n) (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (hE : E.Bounded (inputScale I^11*2^((n+1)/2))
      (inputScale I^11*(compressionDictionaryCapacity n+1))
      (inputScale I^11*(compressionDictionaryCapacity n+1)))
    (hW : ∀ s, (action s).1.2 ≤ inputScale I^501*2^((n+1)/2))
    (hD : ∀ s, (action s).2 ≤ 36*inputScale I^14*(compressionDictionaryCapacity n+1))
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (WordSampledAction.run E action stream cursor).work ≤ inputScale I^502*2^((n+1)/2) ∧
    (WordSampledAction.run E action stream cursor).cells ≤
      38*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  have h := sampled I hn E action hE 501 (by decide) hW hD stream cursor
  rw [show (501 : ℕ)+1 = 502 from rfl] at h
  exact h

theorem compression (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionBranches.CompressionWords I) :
    (WordMeasuredDecision.compression I (by omega) words).1.2 ≤ inputScale I^502*2^((n+1)/2) ∧
    (WordMeasuredDecision.compression I (by omega) words).2 ≤
      38*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  unfold WordMeasuredDecision.compression WordMeasuredDecision.asAction
  apply sampled_501 I (by omega)
  · apply bounded_mono _ (WordSeedScalarBounds.compression_bounded_scale I _ _ _ _ _)
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by unfold inputScale; omega) (by decide : 6 ≤ 11))
    · exact (Nat.pow_le_pow_right (by unfold inputScale; omega) (by decide : 5 ≤ 11)).trans
        (Nat.le_mul_of_pos_right _ (by omega))
    · exact (Nat.pow_le_pow_right (by unfold inputScale; omega) (by decide : 5 ≤ 11)).trans
        (Nat.le_mul_of_pos_right _ (by omega))
  · exact WordActionBounds.compression_source_work I hn hscale
  · intro s
    apply (SampledCompressionCells.cells (CompressionData.mk I) (by omega) s).trans
    have hp := Nat.mul_le_mul_right (compressionDictionaryCapacity n+1)
      (Nat.pow_le_pow_right (n := inputScale I) (by unfold inputScale; omega) (by decide : 12 ≤ 14))
    have ht : inputScale I^14*(compressionDictionaryCapacity n+1) ≤
        36*inputScale I^14*(compressionDictionaryCapacity n+1) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide))
    exact hp.trans ht

theorem representation (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionBranches.RepresentationWords I) :
    (WordMeasuredDecision.representation I (by omega) hlog words).1.2 ≤ inputScale I^502*2^((n+1)/2) ∧
    (WordMeasuredDecision.representation I (by omega) hlog words).2 ≤
      38*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  unfold WordMeasuredDecision.representation WordMeasuredDecision.asAction
  dsimp only [WordMeasuredDecision.representationGenerator]
  apply sampled_501 I (by omega)
  · exact WordSeedHistoryBounds.bucketHistory_bounded I (by omega) _ _
  · exact WordActionBounds.representation_source_work I hn hlog hscale
  · intro s
    exact RepresentationTrialCells.cells I (by omega) hlog hscale s _

theorem round (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionRound.Words I) :
    (WordMeasuredDecision.round I hn hlog words).1.2 ≤ inputScale I^503*2^((n+1)/2) ∧
    (WordMeasuredDecision.round I hn hlog words).2 ≤
      40*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  have hc := compression I hn hscale words.1
  have hr := representation I hn hlog hscale words.2
  have hw := add_work (inputScale I) (2^((n+1)/2)) 502 _
    (by unfold inputScale; omega) Nat.one_le_two_pow (by decide)
    (show (WordMeasuredDecision.round I hn hlog words).1.2 ≤ _ from by
      change _+_+3 ≤ _
      omega)
  rw [show (502 : ℕ)+1 = 503 from rfl] at hw
  refine ⟨hw,?_⟩
  have hl : 24 ≤ inputScale I^14*(compressionDictionaryCapacity n+1) := by
    have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
    have hp : inputScale I ≤ inputScale I^14 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < inputScale I) (by decide : 1 ≤ 14)
    exact (show 24 ≤ inputScale I by omega).trans (hp.trans (Nat.le_mul_of_pos_right _ (by omega)))
  change max _ (_+8)+16 ≤ _
  have hc' := hc.2
  have hr' := hr.2
  rw [Nat.mul_assoc 38] at hc' hr'
  rw [Nat.mul_assoc 40]
  omega

private theorem repetition_work (u H r k W : ℕ) (hu : 3 ≤ u) (hH : 1 ≤ H)
    (hW : W ≤ u^r*(u^k*H+1)+1) : W ≤ u^(r+k+1)*H := by
  have hp : u^r ≤ u^(r+k)*H :=
    (Nat.pow_le_pow_right (by omega : 0 < u) (Nat.le_add_right r k)).trans
      (Nat.le_mul_of_pos_right _ hH)
  have hs : 1 ≤ u^(r+k)*H := Nat.mul_pos (pow_pos (by omega) _) hH
  have he : u^r*(u^k*H) = u^(r+k)*H := by rw [←Nat.mul_assoc,←pow_add]
  rw [Nat.mul_add,Nat.mul_one,he] at hW
  calc
    W ≤ 3*(u^(r+k)*H) := by omega
    _ ≤ u*(u^(r+k)*H) := Nat.mul_le_mul_right _ hu
    _ = _ := by rw [←Nat.mul_assoc,←pow_succ']

theorem repeated_work (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) :
    (WordMeasuredDecision.repeated I hn hscale words).1.2 ≤ inputScale I^624*2^((n+1)/2) := by
  rw [WordMeasuredDecision.repeated,DecisionRepetitionCells.value]
  have h := repetition_work (inputScale I) (2^((n+1)/2)) 120 503 _
    (by unfold inputScale; omega) Nat.one_le_two_pow
    (DecisionRepetition.work
      (fun x => (WordMeasuredDecision.round I hn (roundLogBudget I (by omega) hscale) x).1)
      words _ (fun x => (round I hn (roundLogBudget I (by omega) hscale) hscale x).1))
  rw [show (120 : ℕ)+503+1 = 624 from rfl] at h
  exact h

theorem repeated_cells (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) :
    (WordMeasuredDecision.repeated I hn hscale words).2 ≤ writableWordLimit I := by
  let u := inputScale I
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hC : 1 ≤ C := Nat.one_le_pow _ _ (by decide)
  have h := DecisionRepetitionCells.cells
    (WordMeasuredDecision.round I hn (roundLogBudget I (by omega) hscale)) words
    (40*u^14*(C+1)) (fun x => (round I hn _ hscale x).2)
  apply h.trans
  change 40*u^14*(C+1)+8 ≤ u^15*C
  have hc : C+1 ≤ 2*C := by omega
  have hs : 40*u^14*(C+1) ≤ 80*u^14*C := by
    calc
      _ ≤ 40*u^14*(2*C) := Nat.mul_le_mul_left _ hc
      _ = _ := by ring
  have h8 : 8 ≤ u^14*C := by
    have hpow : u ≤ u^14 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 14)
    exact (show 8 ≤ u by omega).trans (hpow.trans (Nat.le_mul_of_pos_right _ hC))
  have ht : 81*u^14*C ≤ u^15*C := by
    calc
      _ ≤ u*u^14*C := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by rw [←pow_succ']
  nlinarith only [hs,ht,h8]

end LowSpaceSubsetSum.WordMeasuredBounds

end

end OAI
