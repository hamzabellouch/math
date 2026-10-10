import Mathlib
import OAI.Analysis.MatrixSigning.Machines.TerminalVectorReplace

namespace OAI

section

namespace KS.W19.TerminalVectorReplace

theorem ofFn_set {n : ℕ} (f : Fin n → List Bool) (i : Fin n) (a : List Bool) :
    (List.ofFn f).set i.val a = List.ofFn (Function.update f i a) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hji : j < n := by simpa using hk
    simp only [List.getElem_set, List.getElem_ofFn]
    by_cases he : i.val = j
    · have hef : (⟨j,hji⟩ : Fin n) = i := Fin.ext he.symm
      simp only [he,↓reduceIte]
      change a = Function.update f i a (⟨j,hji⟩ : Fin n)
      rw [hef,Function.update_self]
    · have hef : (⟨j,hji⟩ : Fin n) ≠ i := by
        intro h
        exact he (congrArg Fin.val h).symm
      simp [he,Function.update_of_ne hef]

theorem zeroPayloads_ofFn (n : ℕ) : zeroPayloads n = List.ofFn (fun _ : Fin n => KS.W01.encodeRat 0) := by
  simp [zeroPayloads,List.ofFn_const]

def sparsePayloads (n j : ℕ) (c : ℚ) : List (List Bool) :=
  ((zeroPayloads n).set 0 (KS.W01.encodeRat c)).set j (KS.W01.encodeRat 1)

def sparseVector {n : ℕ} (j : Fin (n+1)) (c : ℚ) : Fin (n+1) → ℚ :=
  Pi.single 0 c + Pi.single j 1

theorem sparse_tape {n : ℕ} (j : Fin (n+1)) (hj : j ≠ 0) (c : ℚ) :
    (sparsePayloads (n+1) j.val c).flatMap KS.W01.frame =
      KS.W12.RowDot.vectorTape (sparseVector j c) := by
  unfold sparsePayloads
  erw [zeroPayloads_ofFn,ofFn_set _ (0 : Fin (n+1)),ofFn_set _ j]
  unfold KS.W12.RowDot.vectorTape
  congr 2
  funext i
  by_cases hij : i = j
  · subst i
    simp [sparseVector,hj]
  · by_cases hi0 : i = 0
    · subst i
      simp [sparseVector,Ne.symm hj]
    · simp [Function.update_of_ne,hij,hi0,sparseVector]

theorem sparseVector_zeroPivot {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (j : Fin (n+1)) :
    sparseVector j (-(M j j+1)/(2*M 0 j)) = KS.W17.zeroPivotWitness M 0 j := rfl

end KS.W19.TerminalVectorReplace

end

end OAI
