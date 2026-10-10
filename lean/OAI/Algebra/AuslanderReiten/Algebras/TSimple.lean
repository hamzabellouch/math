import OAI.Algebra.AuslanderReiten.Algebras.SimpleModule
import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtension

namespace OAI

noncomputable section

namespace ArExplicit
namespace TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def baseProjection : TrivialExtension k A →ₐ[k] A where
  toFun a := a.base
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

end TrivialExtension

namespace T

variable {k : Type*} [Field k] (q : k)

def simpleCharacter : T k q →ₐ[k] k where
  toFun a := a.base.coeff .f
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one]

end T

namespace Resolution

variable {k : Type*} [Field k] (q : k)

instance : Module (T k q) (Simple q) :=
  Module.compHom (Simple q) TrivialExtension.baseProjection.toRingHom

@[simp] theorem t_smul_simple (a : T k q) (s : Simple q) :
    a • s = a.base • s := rfl

instance : IsScalarTower k (T k q) (Simple q) where
  smul_assoc r a s := by
    change (r • a.base) • s = r • (a.base • s)
    exact smul_assoc r a.base s

theorem t_simple_character (a : T k q) (s : Simple q) :
    simpleCoordinate q (a • s) = a.base.coeff .f * simpleCoordinate q s :=
  simpleCoordinate_smul q a.base s

theorem dual_ideal_annihilates_simple (φ : Module.Dual k (BaseAlgebra k q)) (s : Simple q) :
    TrivialExtension.inr φ • s = (0 : Simple q) := by
  change (0 : BaseAlgebra k q) • s = 0
  exact zero_smul _ _

end Resolution
end ArExplicit

end

end OAI
