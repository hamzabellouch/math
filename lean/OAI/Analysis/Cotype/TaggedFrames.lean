import OAI.Analysis.Cotype.PatternPairing

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {k m : ℕ}

def taggedPrimal (u : Fin m → Cube k) (i : Fin m) : Cube (k+m+m) :=
  Fin.append (Fin.append (u i) (unitIndex i)) (fun _ : Fin m => false)

def taggedDual (v : Fin m → Cube k) (D : Fin m × Fin m → Bool) (j : Fin m) : Cube (k+m+m) :=
  Fin.append (Fin.append (v j) (fun i => D (i,j))) (unitIndex j)

theorem binaryFrame_of_coordinates {n r : ℕ} (U : Fin r → Cube n) (t : Fin r → Fin n)
    (ht : ∀ i j, binaryBit (U i (t j)) = if i = j then 1 else 0) : BinaryFrame U := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have h := congrFun hc (t j)
  simpa [Finset.sum_apply, ht] using h

theorem taggedPrimal_frame (u : Fin m → Cube k) : BinaryFrame (taggedPrimal u) := by
  apply binaryFrame_of_coordinates _ (fun j => Fin.castAdd m (Fin.natAdd k j))
  intro i j
  simp [taggedPrimal, unitIndex, binaryBit, eq_comm]

theorem taggedDual_frame (v : Fin m → Cube k) (D : Fin m × Fin m → Bool) :
    BinaryFrame (taggedDual v D) := by
  apply binaryFrame_of_coordinates _ (fun j => Fin.natAdd (k+m) j)
  intro i j
  simp [taggedDual, unitIndex, binaryBit, eq_comm]

theorem taggedFrames_pairing (u v : Fin m → Cube k) (D : Fin m × Fin m → Bool)
    (i j : Fin m) :
    character (taggedDual v D j) (taggedPrimal u i) = character (v j) (u i) * sign (D (i,j)) := by
  change character (cubeJoin (k+m) m (cubeJoin k m (v j, fun i => D (i,j)), unitIndex j))
    (cubeJoin (k+m) m (cubeJoin k m (u i, unitIndex i), fun _ => false)) = _
  rw [character_join, character_join, character_symm (fun i => D (i,j)), character_unitIndex]
  have hz : character (unitIndex j) (fun _ : Fin m => false) = 1 := by
    simp [character, sign]
  rw [hz, mul_one]

def taggedCovector (hm : 0 < m) (v : Cube k) (s : Cube m) : Cube (k+m+m) :=
  Fin.append (Fin.append v s) (unitIndex ⟨0,hm⟩)

theorem taggedCovector_frame (hm : 0 < m) (v : Cube k) (s : Cube m) :
    BinaryFrame (fun _ : Fin 1 => taggedCovector hm v s) := by
  exact (taggedDual_frame (fun _ : Fin m => v) (fun ij => s ij.1)).comp
    (fun _ : Fin 1 => (⟨0,hm⟩ : Fin m)) (fun _ _ _ => Subsingleton.elim _ _)

theorem taggedCovector_pairing (hm : 0 < m) (u : Fin m → Cube k) (v : Cube k)
    (s : Cube m) (i : Fin m) :
    character (taggedCovector hm v s) (taggedPrimal u i) = character v (u i) * sign (s i) := by
  change character (cubeJoin (k+m) m (cubeJoin k m (v,s), unitIndex ⟨0,hm⟩))
    (cubeJoin (k+m) m (cubeJoin k m (u i,unitIndex i),fun _ => false)) = _
  rw [character_join, character_join, character_symm s, character_unitIndex]
  have hz : character (unitIndex (⟨0,hm⟩ : Fin m)) (fun _ : Fin m => false) = 1 := by
    simp [character, sign]
  rw [hz, mul_one]

end Cotype

end

end OAI
