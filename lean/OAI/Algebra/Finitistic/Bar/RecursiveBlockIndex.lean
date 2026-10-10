import OAI.Algebra.Finitistic.Bar.RecursiveTotalFlatten
import OAI.Algebra.Finitistic.Bar.BlockIndexEquiv

namespace OAI
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar

/-- Recursive total diagonals record exactly r+1 block lengths; the final
input degree is the last block length. -/
def blocks (r : ℕ) : {n : ℕ} → Index r n → Blocks r := by
  induction r with
  | zero => exact fun {n} _ => n
  | succ r ih => exact fun ⟨p,t⟩ => (p.val.1, ih t)

@[simp] theorem total_blocks (r n : ℕ) (t : Index r n) :
    total r (blocks r t) = n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    change i + total r (blocks r t) = n
    rw [ih, h]

/-- Recover the successive diagonal choices from the literal block lengths. -/
def indexOfBlocks : (r : ℕ) → (b : Blocks r) → Index r (total r b)
  | 0, _ => ()
  | r+1, (i,b) => ⟨⟨⟨i,total r b⟩,rfl⟩,indexOfBlocks r b⟩

def castIndex {r n m : ℕ} (h : n=m) (t : Index r n) : Index r m := h ▸ t

@[simp] theorem blocks_castIndex {r n m : ℕ} (h : n=m) (t : Index r n) :
    blocks r (castIndex h t) = blocks r t := by subst m; rfl

@[simp] theorem blocks_indexOfBlocks (r : ℕ) (b : Blocks r) :
    blocks r (indexOfBlocks r b) = b := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases b with ⟨i,b⟩
    change (i, blocks r (indexOfBlocks r b)) = (i,b)
    rw [ih]

theorem blocks_injective (r n : ℕ) : Function.Injective (@blocks r n) := by
  induction r generalizing n with
  | zero => intro t s _; cases t; cases s; rfl
  | succ r ih =>
    rintro ⟨⟨⟨i,q⟩,h⟩,t⟩ ⟨⟨⟨j,p⟩,g⟩,s⟩ e
    change (i,blocks r t) = (j,blocks r s) at e
    have hi := congrArg Prod.fst e
    dsimp at hi
    subst j
    have hq : q=p := by omega
    subst p
    have ht := ih q (congrArg Prod.snd e)
    subst s
    rfl

/-- Actual equivalence used to flatten the recursively nested finite diagonals. -/
def blockIndexEquiv (r n : ℕ) : Index r n ≃ {b : Blocks r // total r b=n} where
  toFun t := ⟨blocks r t,total_blocks r n t⟩
  invFun b := castIndex b.property (indexOfBlocks r b.val)
  left_inv t := by apply blocks_injective r n; simp
  right_inv b := by apply Subtype.ext; simp

/-- The recursive total index is exactly the manuscript's full-degree D/X shape. -/
def shapeIndexEquiv (r n : ℕ) : Index r n ≃ Multibar.Indexed.Shape (r+n) r :=
  (blockIndexEquiv r n).trans (Multibar.Indexed.blockDegreeEquiv r n)
end DerivedBar.RecursiveTotal

end

end OAI
