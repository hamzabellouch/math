import Mathlib
import OAI.Computability.MinUncut.Search.FiniteQueryFamily
import OAI.Computability.MinUncut.Estimates.TableTestFunctions
import OAI.Computability.MinUncut.Estimates.ComparisonSoundness

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I] {m n : ℕ}

def comparison (q q' : FamilyQuestion Name I) (P : FamilyAlphabet q → Bool)
    (P' : FamilyAlphabet q' → Bool) : QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  ⟨⟨q,P⟩,⟨q',P'⟩,true⟩

lemma comparison_failure (f : ProofFamily Name I) (q q' : FamilyQuestion Name I)
    (P : FamilyAlphabet q → Bool) (P' : FamilyAlphabet q' → Bool) :
    ((comparison q q' P P').failure f.queryAnswer:ℝ)=
      disagreement (f.queryAnswer q P) (f.queryAnswer q' P') := by
  unfold comparison QueryDemand.failure disagreement
  cases f.queryAnswer q P <;> cases f.queryAnswer q' P' <;> simp

def testQuery (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) (z : Code m n)
    (t : ScoreIndex m n → Bool) : Test → QueryDemand (A := FamilyAlphabet (Name := Name) (I := I))
  | .first => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => t (false,labelCode B a)) (fun a => t (true,labelCode B a))
  | .second => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => t (true,labelCode B a)) (fun a => t (true,labelCode C a))
  | .third => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => Function.update (fun z => t (true,z)) z true (labelCode B a))
    (fun a => Function.update (fun z => t (true,z)) z false (labelCode B a))
  | .fourth => comparison (.inl U) (.inr (secondQuestion U h pos))
    (fun a => t (true,labelCode (pullbackFaces (projection U h pos) C) a))
    (fun a => t (true,labelCode C a))

def testFunctional (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n)
    (z : Code m n) (t : ScoreIndex m n → Bool) : Test → ℝ
  | .first => firstTable (f.second (secondQuestion U h pos)) B t
  | .second => secondTable (f.second (secondQuestion U h pos)) B C t
  | .third => thirdTable (f.second (secondQuestion U h pos)) B z t
  | .fourth => fourthTable (f.first U) (f.second (secondQuestion U h pos))
    (pullbackFaces (projection U h pos) C) C t

lemma testQuery_failure (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n)
    (z : Code m n) (t : ScoreIndex m n → Bool) (j : Test) :
    ((testQuery U h pos B C z t j).failure f.queryAnswer:ℝ)=testFunctional f U h pos B C z t j := by
  cases j <;> exact comparison_failure f _ _ _ _
end MinUncut.Outer

end
end

end OAI
