import OAI.NumberTheory.Catalan.Estimates.PalindromicExtractedEntries

namespace OAI

section

noncomputable section

namespace InternalCatalan

def palindromicExtractedResidueMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicExtractedFilteredEntry p r.2 r.1 k.1 k.2

theorem palindromicExtractedResidueMatrix_eq_blocks {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) :
    palindromicExtractedResidueMatrix p = palindromicResidueBlockMatrix p := by
  ext r k
  exact palindromicExtractedFilteredEntry_eq_fixedB hp r.2 r.1 k.1 k.2

theorem palindromicExtractedResidueMatrix_mul_columnChange {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) :
    palindromicExtractedResidueMatrix p * palindromicResidueColumnChange p =
      palindromicReducedBlockMatrix p := by
  rw [palindromicExtractedResidueMatrix_eq_blocks hp]
  exact palindromicResidueBlockMatrix_mul_columnChange (by omega)

theorem det_palindromicExtractedResidueMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp : 260 < p)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicExtractedResidueMatrix p).det ≠ 0 := by
  rw [palindromicExtractedResidueMatrix_eq_blocks hp]
  exact det_palindromicResidueBlockMatrix_ne_zero_of_fixed (by omega) h0 hplus hminus

end InternalCatalan

end

end

end OAI
