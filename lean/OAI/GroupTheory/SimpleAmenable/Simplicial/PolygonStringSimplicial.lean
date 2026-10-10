import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStringNormalization

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonStringSimplicial

open Classical CategoryTheory
open scoped Simplicial
namespace PolygonObject
variable {a : ℕ}

noncomputable def stringSimplicial (a : ℕ) : SimplicialObject Cat.{0,0} where
  obj n := Cat.of (StringGroupoid a n.unop.len)
  map f := (stringReindex f.unop.toOrderHom.toFunctor).toCatHom
  map_id n := by
    apply Cat.ext
    exact stringReindex_id n.unop.len
  map_comp f g := by
    apply Cat.ext
    exact stringReindex_comp g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor

@[simp] theorem stringSimplicial_face (n : ℕ) (j : Fin (n+2)) :
    ((stringSimplicial a).δ j).toFunctor=stringFace j := rfl

noncomputable def stringDoubleNerve (a : ℕ) : SimplicialObject SSet :=
  stringSimplicial a ⋙ nerveFunctor

@[simp] theorem stringDoubleNerve_obj (n : ℕ) :
    (stringDoubleNerve a).obj (Opposite.op ⦋n⦌)=nerve (StringGroupoid a n) := rfl

end PolygonObject
end PolygonStringSimplicial

end SimpleAmenable
end
end

end OAI
