import OAI.NumberTheory.Ostmann.Tree.QuartetFamily

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

def pairLeaf (M : Leaves 1 → Fˣ) (side : Bool) : Fˣ := M (fun _ => side)

theorem pairLeaf_free (a : Bool) (free held : Fˣ) :
    pairLeaf (pairAssignment a free held) a = free := by
  cases a <;> simp [pairLeaf, pairAssignment, Density.join]

theorem pairLeaf_held (a : Bool) (free held : Fˣ) :
    pairLeaf (pairAssignment a free held) (!a) = held := by
  cases a <;> simp [pairLeaf, pairAssignment, Density.join]

theorem pairAssignment_recover (a : Bool) (M : Leaves 1 → Fˣ) :
    pairAssignment a (pairLeaf M a) (pairLeaf M (!a)) = M := by
  funext v
  have hv : v = fun _ => v 0 := by
    funext i
    exact congrArg v (Subsingleton.elim i 0)
  cases a <;> cases h : v 0 <;>
    simp only [pairAssignment, Bool.false_eq_true, ↓reduceIte, Density.join,
      h, Bool.not_false, Bool.not_true, pairLeaf] <;>
    apply congrArg M <;> simpa only [h] using hv.symm

theorem leafProduct_pairLeaf (a : Bool) (M : Leaves 1 → Fˣ) :
    Parameters.leafProduct M = pairLeaf M a * pairLeaf M (!a) := by
  rw [← leafProduct_pairAssignment, pairAssignment_recover]

def crossFiberEquiv (a b : Bool) (m : Fˣ) :
    (Fˣ × Fˣ × Fˣ) ≃ {M : Leaves 2 → Fˣ // Parameters.leafProduct M = m} where
  toFun x := ⟨crossAssignment a b m x.1 x.2.1 x.2.2,
    product_crossAssignment a b m x.1 x.2.1 x.2.2⟩
  invFun M := (pairLeaf (Density.left M.val) (!a),
    pairLeaf (Density.right M.val) (!b), pairLeaf (Density.left M.val) a)
  left_inv x := by
    rcases x with ⟨h,k,z⟩
    simp only [crossAssignment, Density.left_join, Density.right_join,
      pairLeaf_free, pairLeaf_held]
  right_inv M := by
    apply Subtype.ext
    have hm := M.property
    rw [Density.leafProduct_split, leafProduct_pairLeaf a, leafProduct_pairLeaf b] at hm
    have hf : m / (pairLeaf (Density.left M.val) a * pairLeaf (Density.left M.val) (!a) *
        pairLeaf (Density.right M.val) (!b)) = pairLeaf (Density.right M.val) b := by
      apply (div_eq_iff_eq_mul).2
      exact hm.symm.trans (by ac_rfl)
    change Density.join
      (pairAssignment a (pairLeaf (Density.left M.val) a) (pairLeaf (Density.left M.val) (!a)))
      (pairAssignment b _ (pairLeaf (Density.right M.val) (!b))) = M.val
    rw [hf, pairAssignment_recover, pairAssignment_recover, Density.join_left_right]

theorem crossFiberEquiv_apply (a b : Bool) (m h k z : Fˣ) :
    ((crossFiberEquiv a b m) (h,k,z)).val = crossAssignment a b m h k z := rfl

end
end Ostmann.Tree.Quartet

end OAI
