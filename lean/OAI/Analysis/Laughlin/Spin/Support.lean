import OAI.Analysis.Laughlin.Spin.Basic

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericDescendant_off (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z+n) :
    genericDescendant A B z hA hB n i = 0 := by
  induction n generalizing i with
  | zero =>
    simpa [genericDescendant,genericHighest] using
      extendWeightSlice_off A B z hA hB (fun p => highestUnit A B z p.val) i (by omega)
  | succ n ih =>
    rw [genericDescendant_succ]
    change (∑ j, totalRaise A B j i * genericDescendant A B z hA hB n j) = 0
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
    have h1 : (if h : 0 < i.1.val then
        genericDescendant A B z hA hB n (⟨i.1.val-1,by omega⟩,i.2) * ladder A (i.1.val-1) else 0) = 0 := by
      split_ifs with h
      · rw [ih _ (by dsimp; omega),zero_mul]
      · rfl
    have h2 : (if h : 0 < i.2.val then
        genericDescendant A B z hA hB n (i.1,⟨i.2.val-1,by omega⟩) * ladder B (i.2.val-1) else 0) = 0 := by
      split_ifs with h
      · rw [ih _ (by dsimp; omega),zero_mul]
      · rfl
    rw [h1,h2,add_zero]

theorem genericUnitDescendant_off (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z+n) :
    genericUnitDescendant A B z hA hB n i = 0 := by
  simp only [genericUnitDescendant,Pi.smul_apply,smul_eq_mul,genericDescendant_off A B z n hA hB i hi,mul_zero]

end Laughlin.Spin

end OAI
