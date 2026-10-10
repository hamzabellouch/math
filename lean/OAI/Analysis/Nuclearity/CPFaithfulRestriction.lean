import OAI.Analysis.Nuclearity.MatrixCPAmplification

namespace OAI

/-! Complete positivity can be tested after a faithful star homomorphism.
This lets an operator-valued cpc projection be viewed as a map into its
actual closed commutant algebra. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

variable {A B C : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

lemma completelyPositive_of_faithful_postcomp (φ : A →L[ℂ] B)
    (ι : B →⋆ₙₐ[ℂ] C) (hι : Function.Injective ι)
    (hφ : CompletelyPositive ((starHomContinuousLinear ι).comp φ)) :
    CompletelyPositive φ := by
  intro n M hM
  let j := CStarMatrix.mapₙₐ ι (n := Fin n)
  have hj : Function.Injective j := by
    intro X Y h
    ext i k
    apply hι
    exact congrArg (fun N : CStarMatrix (Fin n) (Fin n) C => N i k) h
  apply (NonUnitalStarAlgHom.map_le_map_iff j hj).mp
  rw [map_zero]
  exact hφ n M hM

end WeakPureInfiniteness

end

end OAI
