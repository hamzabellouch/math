import OAI.Analysis.WeakInfiniteness.FaithfulRepresentation

namespace OAI

/-! The universal GNS representation is unital for a unital algebra. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

universe u
variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma universalGNSRepresentation_one : universalGNSRepresentation A 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext f
  let y : lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2 := x
  change f.gnsStarAlgHom 1 (y f) = y f
  rw [map_one]
  rfl

def universalGNSUnitalRepresentation :
    A →⋆ₐ[ℂ] (universalGNSHilbert A →L[ℂ] universalGNSHilbert A) :=
  { universalGNSRepresentation A with
    map_one' := universalGNSRepresentation_one A
    commutes' := fun c => by
      change universalGNSRepresentation A (algebraMap ℂ A c) = _
      rw [Algebra.algebraMap_eq_smul_one, map_smul, universalGNSRepresentation_one A,
        Algebra.algebraMap_eq_smul_one] }

lemma universalGNSUnitalRepresentation_injective :
    Function.Injective (universalGNSUnitalRepresentation A) :=
  universalGNSRepresentation_injective A

end WeakPureInfiniteness

end

end OAI
