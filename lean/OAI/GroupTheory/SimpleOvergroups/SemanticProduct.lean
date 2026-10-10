import Mathlib
import OAI.GroupTheory.BooneHigman.MonoidAlgebras
import OAI.GroupTheory.SimpleOvergroups.ContractedNormalForms
import OAI.GroupTheory.SimpleOvergroups.FirstFamilies
import OAI.GroupTheory.SimpleOvergroups.VariableCode

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open scoped Classical
open FiniteAlgebraicEnvelopes Bootstrap
open ContextualEncoding
namespace SemanticProduct
variable {A K : Type*} [DecidableEq A] [MonoidWithZero K]
  (P : NormalPresentation (FreeMonoid A) K)

abbrev Mon := FiniteAlgebraicEnvelopes.ZeroProduct.Mon K PartialAffine.monoid

def pairEval : FreeMonoid (ProductFamily.Letter A) →* K × PartialAffine.monoid where
  toFun w := (P.q (FreeMonoid.ofList (Projection.left w.toList)),PartialAffine.wordValue (Projection.right w.toList))
  map_one' := by simp only [FreeMonoid.toList_one, Projection.left, List.filterMap_nil,
    FreeMonoid.ofList_nil, map_one]; rfl
  map_mul' u v := by
    apply Prod.ext
    · simp only [FreeMonoid.toList_mul,Projection.left_append,FreeMonoid.ofList_append,map_mul]
      rfl
    · apply Subtype.ext
      simp [PartialAffine.wordValue,PartialAffine.value]

def evaluation : FreeMonoid (ProductFamily.Letter A) →* Mon (K:=K) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair K PartialAffine.monoid).comp (pairEval P)

omit [DecidableEq A] in
 theorem pairEval_surjective : Function.Surjective (pairEval P) := by
  rintro ⟨x,y⟩
  obtain ⟨u,rfl⟩ := P.surjective x
  obtain ⟨v,rfl⟩ := PartialAffine.wordValue_surjective y
  refine ⟨FreeMonoid.ofList (u.toList.map Sum.inl++v.map Sum.inr),?_⟩
  simp [pairEval,Projection.left,Projection.right,List.filterMap_map]

omit [DecidableEq A] in
 theorem evaluation_surjective : Function.Surjective (evaluation P) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair_surjective _ _).comp (pairEval_surjective P)

def normal (w : List (ProductFamily.Letter A)) : List A :=
  (P.normal (FreeMonoid.ofList (Projection.left w))).toList

def value (w : List (ProductFamily.Letter A)) : Option (ProductFamily.Key A) :=
  ProductFamily.combine P.omega.toList (normal P w,PartialAffine.testedClass (Projection.right w))

omit [DecidableEq A] in
 theorem normal_eq_iff (u v : List (ProductFamily.Letter A)) : normal P u = normal P v ↔
    P.q (FreeMonoid.ofList (Projection.left u)) = P.q (FreeMonoid.ofList (Projection.left v)) := by
  rw [P.complete]
  exact FreeMonoid.toList.injective.eq_iff

omit [DecidableEq A] in
 theorem normal_eq_zero (w : List (ProductFamily.Letter A)) : normal P w = P.omega.toList ↔
    P.q (FreeMonoid.ofList (Projection.left w)) = 0 := by
  change (P.normal (FreeMonoid.ofList (Projection.left w))).toList = P.omega.toList ↔ _
  rw [FreeMonoid.toList.injective.eq_iff,P.normal_eq_zero_iff]

 theorem value_eq_iff (u v : List (ProductFamily.Letter A)) :
    value P u = value P v ↔ evaluation P (FreeMonoid.ofList u) = evaluation P (FreeMonoid.ofList v) := by
  change value P u = value P v ↔
    FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_iff]
  change value P u = value P v ↔
    (P.q (FreeMonoid.ofList (Projection.left u)),PartialAffine.wordValue (Projection.right u)) =
      (P.q (FreeMonoid.ofList (Projection.left v)),PartialAffine.wordValue (Projection.right v)) ∨
    P.q (FreeMonoid.ofList (Projection.left u)) = 0 ∧ P.q (FreeMonoid.ofList (Projection.left v)) = 0
  rw [Prod.ext_iff,←normal_eq_iff P,←normal_eq_zero P,←normal_eq_zero P]
  have hp : PartialAffine.wordValue (Projection.right u) = PartialAffine.wordValue (Projection.right v) ↔
      PartialAffine.testedClass (Projection.right u) = PartialAffine.testedClass (Projection.right v) := by
    rw [PartialAffine.testedClass_eq_iff]
    exact Subtype.ext_iff
  rw [hp]
  by_cases hu : normal P u = P.omega.toList <;>
    by_cases hv : normal P v = P.omega.toList <;>
    simp [value,ProductFamily.combine,hu,hv]
  aesop

 theorem value_eq_none (w : List (ProductFamily.Letter A)) :
    value P w = none ↔ evaluation P (FreeMonoid.ofList w) = 0 := by
  change value P w = none ↔ FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = 0
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_zero]
  change value P w = none ↔ P.q (FreeMonoid.ofList (Projection.left w))=0
  rw [←normal_eq_zero P]
  simp [value,ProductFamily.combine]

 theorem full (f : List A → Part (List A))
    (hf : ∀ w, (P.normal (FreeMonoid.ofList w)).toList ∈ f w)
    (w : List (ProductFamily.Letter A)) : value P w ∈ ProductFamily.test P.omega.toList f w :=
  (Part.mem_map_iff _).mpr ⟨_,hf _,rfl⟩

end SemanticProduct
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
