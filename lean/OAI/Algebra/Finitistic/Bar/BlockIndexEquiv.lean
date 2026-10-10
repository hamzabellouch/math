import OAI.Algebra.Finitistic.Bar.SignedBlockModel

namespace OAI
noncomputable section
namespace DerivedBar.Multibar

/-- The first X uniquely determines the length of the preceding D block. -/
theorem base_run_injective (i j : ℕ) (p q : List Bool)
    (h : List.replicate i false ++ true :: p = List.replicate j false ++ true :: q) :
    i=j ∧ p=q := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simpa using h
    | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ] at h
    | succ j =>
      have ht : List.replicate i false ++ true :: p = List.replicate j false ++ true :: q := by
        simpa only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] using h
      obtain ⟨hij,hpq⟩ := ih j ht
      exact ⟨congrArg Nat.succ hij,hpq⟩

/-- Consecutive block lengths have a unique literal D/X word. -/
theorem pattern_injective (r : ℕ) : Function.Injective (pattern r) := by
  induction r with
  | zero =>
    intro i j h
    change List.replicate i false = List.replicate j false at h
    exact List.length_replicate.symm.trans ((congrArg List.length h).trans List.length_replicate)
  | succ r ih =>
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    obtain ⟨hij,hpq⟩ := base_run_injective i j (pattern r p) (pattern r q) h
    exact Prod.ext hij (ih hpq)

/-- Parse a word of a specified count without changing its block data. -/
def parseOfCount (r : ℕ) (p : List Bool) (h : count p=r) : Blocks r := h ▸ parse p

@[simp] theorem pattern_parseOfCount (r : ℕ) (p : List Bool) (h : count p=r) :
    pattern r (parseOfCount r p h) = p := by
  subst r
  exact pattern_parse p

@[simp] theorem parseOfCount_pattern (r : ℕ) (b : Blocks r) :
    parseOfCount r (pattern r b) (count_pattern r b) = b := by
  apply pattern_injective r
  simp

namespace Indexed

def shapeOfList : (p : List Bool) → Shape p.length (count p)
  | [] => .nil
  | false :: p => .base (shapeOfList p)
  | true :: p => .ideal (shapeOfList p)

@[simp] theorem toList_shapeOfList (p : List Bool) : toList (shapeOfList p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b with
    | false => exact congrArg (false :: ·) ih
    | true => exact congrArg (true :: ·) ih

def castShape {n m r s : ℕ} (hn : n=m) (hr : r=s) (p : Shape n r) : Shape m s := hn ▸ hr ▸ p

@[simp] theorem toList_castShape {n m r s : ℕ} (hn : n=m) (hr : r=s) (p : Shape n r) :
    toList (castShape hn hr p) = toList p := by
  subst m s
  rfl

/-- Construct the degree-indexed tensor shape of a tuple of block lengths. -/
def shapeOfBlocks (r : ℕ) (b : Blocks r) : Shape (r+total r b) r :=
  castShape (length_pattern r b) (count_pattern r b) (shapeOfList (pattern r b))

@[simp] theorem toList_shapeOfBlocks (r : ℕ) (b : Blocks r) :
    toList (shapeOfBlocks r b) = pattern r b := by
  simp [shapeOfBlocks]

def blocksOfShape {n r : ℕ} (p : Shape n r) : Blocks r :=
  parseOfCount r (toList p) (count_toList p)

@[simp] theorem pattern_blocksOfShape {n r : ℕ} (p : Shape n r) :
    pattern r (blocksOfShape p) = toList p := by simp [blocksOfShape]

theorem total_blocksOfShape {n r : ℕ} (p : Shape n r) : r+total r (blocksOfShape p)=n := by
  have h := length_pattern r (blocksOfShape p)
  rw [pattern_blocksOfShape, length_toList] at h
  exact h.symm

/-- Reindex the finite block-length diagonal by the existing tensor shapes.
The shift by r occurs in the degree, not in a hidden tensor-power replacement. -/
def blockDegreeEquiv (r m : ℕ) : {b : Blocks r // total r b=m} ≃ Shape (r+m) r where
  toFun b := castShape (congrArg (r+·) b.property) rfl (shapeOfBlocks r b.val)
  invFun p := ⟨blocksOfShape p, by have := total_blocksOfShape p; omega⟩
  left_inv b := by
    apply Subtype.ext
    apply pattern_injective r
    simp
  right_inv p := by
    apply toList_injective
    simp
end Indexed
end DerivedBar.Multibar

end

end OAI
