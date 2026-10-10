import OAI.Algebra.AuslanderReiten.Algebras.TSimple
import OAI.Algebra.AuslanderReiten.Duality.RightDual

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] (q : k)
local notation "C" => BaseAlgebra k q

instance simpleRightAction : SMul Cᵐᵒᵖ (Simple q) :=
  ⟨fun c s => c.unop.coeff f • s⟩

@[simp] theorem simple_right_smul (c : Cᵐᵒᵖ) (s : Simple q) :
    c • s = c.unop.coeff f • s := rfl

instance simpleRightModule : Module Cᵐᵒᵖ (Simple q) where
  one_smul s := by
    change (1 : k) • s = s
    exact one_smul k s
  mul_smul c d s := by
    change (d.unop * c.unop).coeff f • s = c.unop.coeff f • d.unop.coeff f • s
    rw [← mul_smul, mul_comm]
    rfl
  smul_zero c := by
    change c.unop.coeff f • (0 : Simple q) = 0
    exact smul_zero _
  smul_add c s t := by
    change c.unop.coeff f • (s + t) = c.unop.coeff f • s + c.unop.coeff f • t
    exact smul_add _ _ _
  zero_smul s := by
    change (0 : k) • s = 0
    exact zero_smul k s
  add_smul c d s := by
    change (c.unop.coeff f + d.unop.coeff f) • s = _
    exact add_smul _ _ _

instance : IsScalarTower k Cᵐᵒᵖ (Simple q) where
  smul_assoc a c s := mul_smul a (c.unop.coeff f) s

def generator : Simple q := (LinearMap.range (dU q)).mkQ (vertexF q)

@[simp] theorem generator_coordinate : simpleCoordinate q (generator q) = 1 := rfl

theorem simple_expand (hq : 1 + q ≠ 0) (s : Simple q) :
    s = simpleCoordinate q s • generator q := by
  apply simpleCoordinate_injective q hq
  simp

def rightSimpleDualEquiv (hq : 1 + q ≠ 0) : RightDual k C (Simple q) ≃ₗ[C] Simple q where
  toFun φ := φ.functional (generator q) • generator q
  invFun s := ⟨(simpleCoordinate q).smulRight (simpleCoordinate q s)⟩
  left_inv φ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro s
    change simpleCoordinate q s * simpleCoordinate q
      (φ.functional (generator q) • generator q) = φ.functional s
    rw [map_smul, generator_coordinate, smul_eq_mul, mul_one, simple_expand q hq s]
    simp only [map_smul, smul_eq_mul, generator_coordinate, mul_one]
  right_inv s := by
    change (simpleCoordinate q (generator q) * simpleCoordinate q s) • generator q = s
    rw [generator_coordinate, one_mul]
    exact (simple_expand q hq s).symm
  map_add' φ ψ := by
    change (φ.functional (generator q) + ψ.functional (generator q)) • generator q = _
    exact add_smul _ _ _
  map_smul' c φ := by
    change φ.functional (c.coeff f • generator q) • generator q =
      c • (φ.functional (generator q) • generator q)
    apply simpleCoordinate_injective q hq
    simp [simpleCoordinate_smul, mul_comm]

end ArExplicit.Resolution

end

end OAI
