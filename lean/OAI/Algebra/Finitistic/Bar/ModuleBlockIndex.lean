import OAI.Algebra.Finitistic.Bar.LiteralMultibarCoordinates

namespace OAI
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar

/-- Remove the zero input degree from the list of bar lengths. -/
def moduleBlocks : (r : ℕ) → {n : ℕ} → (t : Index (r+1) n) → Blocks r
  | 0, _, ⟨p,_⟩ => p.val.1
  | r+1, _, ⟨p,t⟩ => (p.val.1, moduleBlocks r t)

theorem total_moduleBlocks (r n : ℕ) (t : Index (r+1) n) :
    total r (moduleBlocks r t) + inputDegree (r+1) t = n := by
  induction r generalizing n with
  | zero => rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩; exact h
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    have ht := ih q t
    change i + total r (moduleBlocks r t) + inputDegree (r+1) t = n
    omega

theorem pattern_moduleBlocks (r n : ℕ) (t : Index (r+1) n) :
    pattern r (moduleBlocks r t) = leadingPattern r n t := by
  induction r generalizing n with
  | zero =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp [moduleBlocks, pattern, leadingPattern, innerPattern]
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    change List.replicate i false ++ true :: pattern r (moduleBlocks r t) = _
    rw [ih q t]
    rfl

/-- The recursive total index attached to a block tuple, with input degree zero. -/
def moduleIndex : (r : ℕ) → (b : Blocks r) → Index (r+1) (total r b)
  | 0, i => ⟨⟨⟨i,0⟩,by exact Nat.add_zero i⟩,()⟩
  | r+1, (i,b) => ⟨⟨⟨i,total r b⟩,rfl⟩,moduleIndex r b⟩

@[simp] theorem inputDegree_moduleIndex (r : ℕ) (b : Blocks r) :
    inputDegree (r+1) (moduleIndex r b) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rcases b with ⟨i,b⟩; exact ih b

@[simp] theorem moduleBlocks_moduleIndex (r : ℕ) (b : Blocks r) :
    moduleBlocks r (moduleIndex r b) = b := by
  induction r with
  | zero => rfl
  | succ r ih => rcases b with ⟨i,b⟩; change (i,moduleBlocks r (moduleIndex r b)) = _; rw [ih]

@[simp] theorem inputDegree_castIndex {r n m : ℕ} (h : n=m) (t : Index r n) :
    inputDegree r (castIndex h t) = inputDegree r t := by subst m; rfl

@[simp] theorem moduleBlocks_castIndex {r n m : ℕ} (h : n=m) (t : Index (r+1) n) :
    moduleBlocks r (castIndex h t) = moduleBlocks r t := by subst m; rfl

/-- All indices are recovered from the blocks and input degree; no quotient of
block tensors or identification of distinct patterns is introduced. -/
theorem moduleBlocks_injective (r n : ℕ) (t s : Index (r+1) n)
    (ht : inputDegree (r+1) t=0) (hs : inputDegree (r+1) s=0)
    (h : moduleBlocks r t=moduleBlocks r s) : t=s := by
  induction r generalizing n with
  | zero =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    rcases s with ⟨⟨⟨j,p⟩,hp⟩,s⟩
    change q=0 at ht
    change p=0 at hs
    subst q p
    have hij : i=j := by omega
    subst j
    cases t; cases s; rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    rcases s with ⟨⟨⟨j,p⟩,hp⟩,s⟩
    change (i,moduleBlocks r t) = (j,moduleBlocks r s) at h
    have hij := congrArg Prod.fst h
    dsimp at hij
    subst j
    have hqp : q=p := by omega
    subst p
    have hts := ih q t s ht hs (congrArg Prod.snd h)
    subst s
    rfl

/-- Exact module-input indexing by the manuscript's tuples of r+1 block lengths. -/
def moduleBlockEquiv (r n : ℕ) :
    {t : Index (r+1) n // inputDegree (r+1) t=0} ≃
      {b : Blocks r // total r b=n} where
  toFun t := ⟨moduleBlocks r t.val, by
    have h := total_moduleBlocks r n t.val
    rw [t.property, Nat.add_zero] at h
    exact h⟩
  invFun b := ⟨castIndex b.property (moduleIndex r b.val), by simp⟩
  left_inv t := by
    apply Subtype.ext
    apply moduleBlocks_injective r n _ _ (by simp) t.property
    simp
  right_inv b := by apply Subtype.ext; simp

/-- Exact full-degree shape index, including the shift by the number of X slots. -/
def moduleShapeEquiv (r n : ℕ) :
    {t : Index (r+1) n // inputDegree (r+1) t=0} ≃
      Multibar.Indexed.Shape (r+n) r :=
  (moduleBlockEquiv r n).trans (Multibar.Indexed.blockDegreeEquiv r n)
end DerivedBar.RecursiveTotal

end

end OAI
