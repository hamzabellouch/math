import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRepresentationHistory
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRunLaw
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredSpace

namespace OAI

/-! # The complete word draw buffer fits below the branch workspace -/

noncomputable section
namespace LowSpaceSubsetSum.WordSamplingBounds

variable {n : ℕ}

theorem family_width (n : ℕ) : 2*RepresentationSetup.blockHalf n 0 ≤ n := by
  unfold RepresentationSetup.blockHalf
  simp only [Matrix.cons_val_zero]
  omega

theorem family_codes (n : ℕ) :
    2^(2*RepresentationSetup.blockHalf n 0) ≤ compressionDictionaryCapacity n := by
  apply (Nat.pow_le_pow_right (by decide)
    (show 2*RepresentationSetup.blockHalf n 0 ≤ 2*(2*RepresentationSetup.blockHalf n 0) by omega)).trans
  exact RepresentationSetup.separator_table_rate_le_capacity

theorem history_normalize (n : ℕ) : WordRealization.historyReads n =
    4*n^4+10*n^3+n+44*2^(2*RepresentationSetup.blockHalf n 0)*
      (2*RepresentationSetup.blockHalf n 0)*n^3 := by
  unfold WordRealization.historyReads
  ring

theorem history_reads (I : Instance n) (hn : 10000 ≤ n) :
    WordRealization.historyReads n ≤ inputScale I^5*(compressionDictionaryCapacity n+1) := by
  let u := inputScale I
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hnu : n ≤ u := by unfold u inputScale; omega
  have hn1 : 1 ≤ u := by omega
  have h34 : n^3 ≤ u^4 :=
    (Nat.pow_le_pow_left hnu 3).trans (Nat.pow_le_pow_right hn1 (by decide : 3 ≤ 4))
  have hn4 : n ≤ u^4 := by
    exact hnu.trans (by simpa only [pow_one] using
      Nat.pow_le_pow_right hn1 (by decide : 1 ≤ 4))
  have hnfour : n^4 ≤ u^4 := Nat.pow_le_pow_left hnu 4
  have hf : 44*2^(2*RepresentationSetup.blockHalf n 0)*
      (2*RepresentationSetup.blockHalf n 0)*n^3 ≤ 44*u^4*C := by
    calc
      _ ≤ 44*C*u*u^3 := by
        gcongr
        · exact family_codes n
        · exact (family_width n).trans hnu
      _ = _ := by ring
  have hp : WordRealization.historyReads n ≤ 59*u^4*(C+1) := by
    rw [history_normalize]
    nlinarith only [h34,hn4,hnfour,hf]
  apply hp.trans
  calc
    _ ≤ u*u^4*(C+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by rw [← pow_succ']

theorem word_width (I : Instance n) : 3*n+1 ≤ wordWidth I := by
  unfold wordWidth inputScale
  omega

def representation (I : Instance n) (hn : 10000 ≤ n) :
    WordRealization.Realization (wordWidth I) (WordRealization.historyReads n)
      ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn) :=
  WordRealization.bucketHistory _ hn _ (word_width I)

theorem representation_probability (I : Instance n) (hn : 10000 ≤ n)
    (P : Option ((canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega)) → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Fin (WordRealization.historyReads n) → Fin (2^wordWidth I))).probability
        (fun words => P (WordProgram.run (WordProgram.finiteStream words)
          (representation I hn).program 0).1) =
      ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).boundedLaw.probability P := by
  rw [← WordProgram.run_probability _ _ (representation I hn).bounded]
  exact (representation I hn).faithful P

end LowSpaceSubsetSum.WordSamplingBounds

end

end OAI
