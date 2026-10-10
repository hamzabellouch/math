import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordDecisionRound

namespace OAI

/-! # Prepared-action costs on every finite word stream

These counters account for the prepared action after seed generation. Seed
construction work and its live buffer are separate from these bounds.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordActionBounds

variable {n : ℕ}

private theorem pow_product_positive (u H k : ℕ) (hu : 0 < u) (hH : 0 < H) :
    1 ≤ u^k*H := Nat.mul_pos (Nat.pow_pos hu) hH

private theorem pow_product_mono (u H j k : ℕ) (hu : 0 < u) (hH : 1 ≤ H)
    (hjk : j ≤ k) : u^j ≤ u^k*H :=
  (Nat.pow_le_pow_right hu hjk).trans (Nat.le_mul_of_pos_right _ hH)

private theorem combine_work (c r : (Bool × ℕ) × ℕ) (T : ℕ)
    (hc : c.1.2 ≤ T) (hr : r.1.2 ≤ T) :
    (WordDecisionRound.combine c r).1.2 ≤ 2*T+3 := by
  change c.1.2+r.1.2+3 ≤ 2*T+3
  omega

private theorem round_work_generic (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (words : WordDecisionRound.Words I) (T : ℕ)
    (hc : (WordDecisionBranches.compression I (by omega) words.1).1.2 ≤ T)
    (hr : (WordDecisionBranches.representation I (by omega) hlog words.2).1.2 ≤ T) :
    (WordDecisionRound.run I hn hlog words).1.2 ≤ 2*T+3 :=
  combine_work _ _ T hc hr

private theorem combine_cells (c r : (Bool × ℕ) × ℕ) (L : ℕ)
    (hc : c.2 ≤ L) (hr : r.2 ≤ 36*L) (hL : 24 ≤ L) :
    (WordDecisionRound.combine c r).2 ≤ 40*L := by
  change max c.2 (r.2+8)+16 ≤ 40*L
  omega

private theorem scale_large (u C : ℕ) (hu : 10000 ≤ u) : 24 ≤ u^14*(C+1) := by
  have hp : u ≤ u^14 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 14)
  have hm : u^14 ≤ u^14*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

private theorem law_nonempty {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) : Nonempty Ω := by
  classical
  by_contra h
  let : IsEmpty Ω := ⟨fun x => h ⟨x⟩⟩
  have ht := μ.total
  simp at ht

theorem compression_source_work (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((CompressionData.mk I).sampler (by omega)).Seed) :
    (SampledCompressionCells.run (CompressionData.mk I) (by omega) s).1.2 ≤
      inputScale I^501*2^((n+1)/2) := by
  let R := (canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega : 10000 ≤ n)
  let t : R.Seed := Classical.choice (law_nonempty R.law)
  have h := PreparedDecisionWork.round I hn (roundLogBudget I (by omega) hscale) hscale (s,t)
  dsimp only [PreparedDecisionRound.run] at h
  rw [SampledCompressionCells.value]
  omega

theorem representation_source_work (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling (by omega)).Seed) :
    (WordDecisionBranches.representationAction I (by omega) hlog s).1.2 ≤
      inputScale I^501*2^((n+1)/2) := by
  let C := (CompressionData.mk I).sampler (by omega : 168000000 ≤ n)
  let t : C.Seed := Classical.choice (law_nonempty C.law)
  have h := PreparedDecisionWork.round I hn hlog hscale (t,s)
  dsimp only [PreparedDecisionRound.run] at h
  simp only [WordDecisionBranches.representationAction,RepresentationTrialCells.value]
  omega

theorem compression_work (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionBranches.CompressionWords I) :
    (WordDecisionBranches.compression I (by omega) words).1.2 ≤
      inputScale I^501*2^((n+1)/2) := by
  unfold WordDecisionBranches.compression WordSeedRealization.execute
  split
  · have hu : 0 < inputScale I := by unfold inputScale; omega
    exact pow_product_positive (inputScale I) (2^((n+1)/2)) 501 hu (Nat.two_pow_pos _)
  · exact compression_source_work I hn hscale _

theorem representation_work (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionBranches.RepresentationWords I) :
    (WordDecisionBranches.representation I (by omega) hlog words).1.2 ≤
      inputScale I^501*2^((n+1)/2) := by
  unfold WordDecisionBranches.representation WordSeedRealization.execute
  split
  · have hu : 0 < inputScale I := by unfold inputScale; omega
    exact pow_product_positive (inputScale I) (2^((n+1)/2)) 501 hu (Nat.two_pow_pos _)
  · exact representation_source_work I hn hlog hscale _

private theorem combine_majorize (u H k W : ℕ) (hu : 3 ≤ u) (hH : 1 ≤ H)
    (hk : 1 ≤ k) (hW : W ≤ 2*(u^k*H)+3) : W ≤ u^(k+1)*H := by
  have hp : u ≤ u^k := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) hk
  have hm : u^k ≤ u^k*H := Nat.le_mul_of_pos_right _ hH
  calc
    W ≤ 3*(u^k*H) := by omega
    _ ≤ u*(u^k*H) := Nat.mul_le_mul_right _ hu
    _ = _ := by rw [←Nat.mul_assoc,←pow_succ']

theorem round_work (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionRound.Words I) :
    (WordDecisionRound.run I hn hlog words).1.2 ≤ inputScale I^502*2^((n+1)/2) := by
  have h := combine_majorize (inputScale I) (2^((n+1)/2)) 501 _
    (by unfold inputScale; omega) Nat.one_le_two_pow (by decide)
    (round_work_generic I hn hlog words _ (compression_work I hn hscale words.1)
      (representation_work I hn hlog hscale words.2))
  rw [show (501 : ℕ)+1 = 502 from rfl] at h
  exact h

theorem compression_cells (I : Instance n) (hn : 180000000 ≤ n)
    (words : WordDecisionBranches.CompressionWords I) :
    (WordDecisionBranches.compression I (by omega) words).2 ≤
      inputScale I^12*(compressionDictionaryCapacity n+1) := by
  unfold WordDecisionBranches.compression WordSeedRealization.execute
  split
  · have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
    have hp : inputScale I ≤ inputScale I^12 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I)
        (by decide : 1 ≤ 12)
    have hm := Nat.le_mul_of_pos_right (inputScale I^12)
      (show 0 < compressionDictionaryCapacity n+1 by omega)
    exact (by omega : 8 ≤ inputScale I^12*(compressionDictionaryCapacity n+1))
  · exact SampledCompressionCells.cells _ (by omega) _

theorem representation_cells (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionBranches.RepresentationWords I) :
    (WordDecisionBranches.representation I (by omega) hlog words).2 ≤
      36*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  unfold WordDecisionBranches.representation WordSeedRealization.execute
  split
  · have hp : 1 ≤ inputScale I^14 := Nat.one_le_pow _ _ (by unfold inputScale; omega)
    have hm : inputScale I^14 ≤ inputScale I^14*(compressionDictionaryCapacity n+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith only [hp,hm]
  · exact RepresentationTrialCells.cells I (by omega) hlog hscale _ _

theorem round_cells (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : WordDecisionRound.Words I) :
    (WordDecisionRound.run I hn hlog words).2 ≤
      40*inputScale I^14*(compressionDictionaryCapacity n+1) := by
  let L := inputScale I^14*(compressionDictionaryCapacity n+1)
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hc : (WordDecisionBranches.compression I (by omega) words.1).2 ≤ L :=
    (compression_cells I hn words.1).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (n := inputScale I)
        (by omega) (by decide : 12 ≤ 14)))
  have hr : (WordDecisionBranches.representation I (by omega) hlog words.2).2 ≤ 36*L := by
    apply (representation_cells I hn hlog hscale words.2).trans
    exact le_of_eq (Nat.mul_assoc _ _ _)
  have h := combine_cells _ _ L hc hr (scale_large _ _ hu)
  exact h.trans (le_of_eq (Nat.mul_assoc _ _ _).symm)

private theorem repeat_majorize (u H r k W : ℕ) (hu : 3 ≤ u) (hH : 1 ≤ H)
    (hW : W ≤ u^r*(u^k*H+1)+1) : W ≤ u^(r+k+1)*H := by
  have hp : u^r ≤ u^(r+k)*H := pow_product_mono u H r (r+k) (by omega) hH (by omega)
  have hs : 1 ≤ u^(r+k)*H := pow_product_positive u H (r+k) (by omega) hH
  have he : u^r*(u^k*H) = u^(r+k)*H := by rw [←Nat.mul_assoc,←pow_add]
  rw [Nat.mul_add,Nat.mul_one,he] at hW
  calc
    W ≤ 3*(u^(r+k)*H) := by omega
    _ ≤ u*(u^(r+k)*H) := Nat.mul_le_mul_right _ hu
    _ = _ := by rw [←Nat.mul_assoc,←pow_succ']

theorem repeated_work (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) :
    (WordDecisionRound.repeated I hn hscale words).1.2 ≤
      inputScale I^623*2^((n+1)/2) := by
  rw [WordDecisionRound.repeated,DecisionRepetitionCells.value]
  have h := repeat_majorize (inputScale I) (2^((n+1)/2)) 120 502 _
    (by unfold inputScale; omega) Nat.one_le_two_pow
    (DecisionRepetition.work _ words _
      (round_work I hn (roundLogBudget I (by omega) hscale) hscale))
  rw [show (120 : ℕ)+502+1 = 623 from rfl] at h
  exact h

theorem repeated_cells (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000)
    (words : Fin (inputScale I^120) → WordDecisionRound.Words I) :
    (WordDecisionRound.repeated I hn hscale words).2 ≤ writableWordLimit I := by
  let u := inputScale I
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hC : 1 ≤ C := Nat.one_le_pow _ _ (by decide)
  have h := DecisionRepetitionCells.cells
    (WordDecisionRound.run I hn (roundLogBudget I (by omega) hscale)) words
    (40*u^14*(C+1)) (round_cells I hn _ hscale)
  change (WordDecisionRound.repeated I hn hscale words).2 ≤ 40*u^14*(C+1)+8 at h
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

end LowSpaceSubsetSum.WordActionBounds

end

end OAI
