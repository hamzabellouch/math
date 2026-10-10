import Mathlib
import OAI.Analysis.Commutator.TracialGNSCorners
import OAI.Analysis.Commutator.VectorFreeGeneration

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M)

lemma inclusion_projection (q : D) (hq : IsStarProjection (inclusion M D hDM q)) :
    IsStarProjection (q:H →L[ℂ] H) :=
  hq.map M.toStarSubalgebra.subtype

def RepresentedCornerBound (U : H →L[ℂ] H) (c : ℝ) (β : ℂ) : Prop :=
  ∀ q : D,IsStarProjection (q:H →L[ℂ] H) →
    subalgebraTrace D ξ q=β → ∀ a : M,
    (q:H →L[ℂ] H)*a*q=a →
    ‖U*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*U‖≤c*‖a‖

include htr in
lemma represented_corner_bound (U : H →L[ℂ] H) (c : ℝ) (β : ℂ)
    (hb : RepresentedCornerBound M ξ D U c β) :
    CornerCommutatorBound (D:=D) M ξ hfaith hone (inclusion M D hDM) R U c β := by
  apply corner_bound M ξ htr hfaith hone (inclusion M D hDM) R U c β
  intro q hq hqt a hl hr
  exact hb q (inclusion_projection M D hDM q hq) hqt a
    (subtype_corner M (inclusion M D hDM q) a hl hr)

end Kadison.VectorGNS

end

end
end

end OAI
