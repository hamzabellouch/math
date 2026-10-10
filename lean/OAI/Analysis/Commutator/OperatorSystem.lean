import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.OperatorSystem

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance operatorSystemDecidableEq (ι : Type*) : DecidableEq ι := Classical.decEq ι

def matrices (S : Submodule ℂ A) (ι : Type*) [Fintype ι] : Submodule ℂ (CStarMatrix ι ι A) where
  carrier := {X | ∀ i j,X i j∈S}
  zero_mem' := by simp
  add_mem' hx hy i j := S.add_mem (hx i j) (hy i j)
  smul_mem' c X hX i j := S.smul_mem c (hX i j)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrices_mem (S : Submodule ℂ A) {ι : Type*} [Fintype ι] (X) :
    X∈matrices S ι ↔ ∀ i j,X i j∈S := Iff.rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrices_one (S : Submodule ℂ A) (h1 : (1 : A)∈S) {ι : Type*} [Fintype ι] :
    (1 : CStarMatrix ι ι A)∈matrices S ι := by
  classical
  intro i j
  by_cases h : i=j <;> simp [CStarMatrix.one_apply,h,h1]

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrices_star (S : Submodule ℂ A) (hs : ∀ a∈S,star a∈S)
    {ι : Type*} [Fintype ι] (X : CStarMatrix ι ι A) (hX : X∈matrices S ι) :
    star X∈matrices S ι := fun i j => hs _ (hX j i)

def mapMatrix (S : Submodule ℂ A) (f : S →ₗ[ℂ] B) {ι : Type*} [Fintype ι] :
    matrices S ι →ₗ[ℂ] CStarMatrix ι ι B where
  toFun X := CStarMatrix.ofMatrix (fun i j => f ⟨X.val i j,X.property i j⟩)
  map_add' X Y := by
    ext i j
    change f (⟨X.val i j,X.property i j⟩+⟨Y.val i j,Y.property i j⟩)=_
    exact f.map_add _ _
  map_smul' c X := by
    ext i j
    change f (c • (⟨X.val i j,X.property i j⟩ : S))=_
    exact f.map_smul c _

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] lemma mapMatrix_apply (S : Submodule ℂ A) (f : S →ₗ[ℂ] B)
    {ι : Type*} [Fintype ι] (X : matrices S ι) (i j : ι) :
    mapMatrix S f X i j=f ⟨X.val i j,X.property i j⟩ := rfl

def IsCompletelyPositive (S : Submodule ℂ A) (f : S →ₗ[ℂ] B) : Prop :=
  ∀ (ι : Type) [Fintype ι] (X : matrices S ι),0 ≤ X.val → 0 ≤ mapMatrix S f X

end Kadison.OperatorSystem

end

end
end

end OAI
