import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationLeaves

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
variable {F : Type*} [Field F]

def productFiberEquiv (k : ℕ) (totals : Leaves k → Fˣ) :
    {M : Leaves (k+2) → Fˣ // (bottomCut k).project M = totals} ≃
      ((v : Leaves k) → {m : Leaves 2 → Fˣ // Parameters.leafProduct m = totals v}) where
  toFun M v := ⟨bottomLeaves k M.val v,
    (bottomLeaves_product k M.val v).trans (congrFun M.property v)⟩
  invFun m := ⟨assembleBottom k (fun v => (m v).val), by
    funext v
    rw [← bottomLeaves_product, bottomLeaves_assemble]
    exact (m v).property⟩
  left_inv M := Subtype.ext (assemble_bottomLeaves k M.val)
  right_inv m := by
    funext v
    apply Subtype.ext
    exact congrFun (bottomLeaves_assemble k (fun v => (m v).val)) v

end
end Ostmann.Tree.QuartetFactorization

end OAI
