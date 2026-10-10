import OAI.Algebra.AuslanderReiten.Modules.Coinduced

namespace OAI

namespace ArExplicit.Coinduced
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

instance : SMul Rᵐᵒᵖ (Coinduced k R) :=
  ⟨fun r x => ⟨{ toFun := fun s => x.functional (r.unop * s)
                 map_add' := fun s t => by simp [mul_add]
                 map_smul' := fun a s => by simp }⟩⟩

@[simp] theorem functional_right (r : Rᵐᵒᵖ) (x : Coinduced k R) (s : R) :
    (r • x).functional s = x.functional (r.unop * s) := rfl

instance : Module Rᵐᵒᵖ (Coinduced k R) where
  one_smul x := by ext s; simp
  mul_smul r t x := by ext s; simp [mul_assoc]
  smul_zero r := by ext s; simp
  smul_add r x y := by ext s; simp
  zero_smul x := by ext s; simp
  add_smul r t x := by ext s; simp [add_mul]

instance : SMulCommClass R Rᵐᵒᵖ (Coinduced k R) where
  smul_comm r t x := by ext s; simp [mul_assoc]
instance : IsScalarTower k Rᵐᵒᵖ (Coinduced k R) where
  smul_assoc a r x := by ext s; simp
instance : SMulCommClass k Rᵐᵒᵖ (Coinduced k R) where
  smul_comm a r x := by ext s; rfl

end ArExplicit.Coinduced

end OAI
