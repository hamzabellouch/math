import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions

namespace OAI

/-!
# Fixed-end path rotation

The explicit tail reversal used in manuscript Lemma `clq:coloured-path`
is proved here. The pivot may be the first vertex, and the last vertex
becomes the successor of the pivot. No path-rotation theorem is assumed.
-/

namespace CycleClique.Construction
/-- Reverse precisely the indices strictly after the pivot. -/
def rotationIndex {r : ℕ} (p : Fin r) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨if i.val ≤ p.val then i.val else r + p.val + 1 - i.val,
    by split_ifs <;> omega⟩

theorem rotationIndex_involutive {r : ℕ} (p : Fin r) :
    Function.Involutive (rotationIndex p) := by
  intro i
  apply Fin.ext
  dsimp [rotationIndex]
  split_ifs <;> omega

theorem rotationIndex_injective {r : ℕ} (p : Fin r) :
    Function.Injective (rotationIndex p) := (rotationIndex_involutive p).injective

@[simp] theorem rotationIndex_zero {r : ℕ} (p : Fin r) : rotationIndex p 0 = 0 := by
  apply Fin.ext
  simp [rotationIndex]

@[simp] theorem rotationIndex_last {r : ℕ} (p : Fin r) :
    rotationIndex p (Fin.last r) = p.succ := by
  apply Fin.ext
  dsimp [rotationIndex]
  split_ifs <;> omega

theorem rotationIndex_range {V : Type*} {r : ℕ} (f : Fin (r + 1) → V) (p : Fin r) :
    Set.range (f ∘ rotationIndex p) = Set.range f := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rotationIndex p i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨rotationIndex p i, congrArg f (rotationIndex_involutive p i)⟩

/-- Rotating a simple path around a neighbour of its last vertex
preserves every vertex and the first endpoint, and makes the pivot's
successor the new last endpoint. -/
theorem rotate_path {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (f : Fin (r + 1) → V) (hf : Function.Injective f)
    (hchain : ∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ))
    (p : Fin r) (hp : G.Adj (f (Fin.last r)) (f p.castSucc)) :
    Function.Injective (f ∘ rotationIndex p) ∧
      (∀ i : Fin r, G.Adj ((f ∘ rotationIndex p) i.castSucc)
        ((f ∘ rotationIndex p) i.succ)) ∧
      (f ∘ rotationIndex p) 0 = f 0 ∧
      (f ∘ rotationIndex p) (Fin.last r) = f p.succ ∧
      Set.range (f ∘ rotationIndex p) = Set.range f := by
  refine ⟨hf.comp (rotationIndex_injective p), ?_, by simp, by simp, rotationIndex_range f p⟩
  intro i
  change G.Adj (f (rotationIndex p i.castSucc)) (f (rotationIndex p i.succ))
  by_cases hlt : i.val < p.val
  · have hleft : rotationIndex p i.castSucc = i.castSucc := by
      apply Fin.ext
      simp only [rotationIndex, Fin.val_castSucc]
      split_ifs <;> omega
    have hright : rotationIndex p i.succ = i.succ := by
      apply Fin.ext
      simp only [rotationIndex, Fin.val_succ]
      split_ifs <;> omega
    simpa [hleft, hright] using hchain i
  · by_cases heq : i = p
    · subst i
      have hleft : rotationIndex p p.castSucc = p.castSucc := by
        apply Fin.ext
        simp [rotationIndex]
      have hright : rotationIndex p p.succ = Fin.last r := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_succ, Fin.val_last]
        split_ifs <;> omega
      simpa [hleft, hright] using hp.symm
    · have hgt : p.val < i.val := by
        have hneq : i.val ≠ p.val := fun h => heq (Fin.ext h)
        omega
      let j : Fin r := ⟨r + p.val - i.val, by omega⟩
      have hleft : rotationIndex p i.castSucc = j.succ := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_castSucc, Fin.val_succ, j]
        split_ifs <;> omega
      have hright : rotationIndex p i.succ = j.castSucc := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_castSucc, Fin.val_succ, j]
        split_ifs <;> omega
      simpa [hleft, hright] using (hchain j).symm

end CycleClique.Construction

end OAI
