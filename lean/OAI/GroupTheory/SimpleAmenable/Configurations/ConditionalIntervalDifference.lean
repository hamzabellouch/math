import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CellGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConditionalIntervalDifference
variable {a m : ℕ}

theorem conditionalAlternatingHom_union (U V : polygonAlgebra a)
    (hd : Disjoint U.val V.val) (s : alternatingGroup (Fin m)) :
    conditionalAlternatingHom (U ⊔ V) s = conditionalAlternatingHom U s*conditionalAlternatingHom V s := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (U ⊔ V) s.val p = conditionalPerm U s.val (conditionalPerm V s.val p)
  by_cases hu : p.2 ∈ U.val <;> by_cases hv : p.2 ∈ V.val
  · exact False.elim (Set.disjoint_left.mp hd hu hv)
  all_goals simp [conditionalPerm,hu,hv]

theorem conditionalAlternatingHom_interval_difference (d : Fin 2) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1) (s : alternatingGroup (Fin m)) :
    (conditionalAlternatingHom (coordinateInterval a d u v) s)⁻¹ *
      conditionalAlternatingHom (coordinateInterval a d u w) s =
      conditionalAlternatingHom (coordinateInterval a d v w) s := by
  rw [coordinateInterval_union d u v w huv hvw hlen,
    conditionalAlternatingHom_union _ _ (coordinateInterval_disjoint d u v v w huv le_rfl hvw hlen)]
  group

end ConditionalIntervalDifference

end SimpleAmenable
end
end

end OAI
