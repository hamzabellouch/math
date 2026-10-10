import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorComplex

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

def cubicInsert (n : ℕ) (ij : Diagonal n) :
    summands k A B P Q n ij →ₗ[E] (complex k A B P Q).X n :=
  (termDirectSumEquiv k A B P Q n).symm.toLinearMap.comp (DFinsupp.lsingle (R := E)
    (M := fun t : Diagonal n => ↥(summands k A B P Q n t)) ij)

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)

def firstCubicEntry (n : ℕ) : (ij : Diagonal (n+3)) →
    summands k A B P Q (n+3) ij →ₗ[E] (complex k A B P Q).X n
  | ⟨(0, _), _⟩ => 0
  | ⟨(1, _), _⟩ => 0
  | ⟨(2, _), _⟩ => 0
  | ⟨(i+3, j), h⟩ => (cubicInsert k A B P Q n ⟨(i,j), by omega⟩).comp
      (map k A B (p i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j))

def secondCubicEntry (n : ℕ) : (ij : Diagonal (n+3)) →
    summands k A B P Q (n+3) ij →ₗ[E] (complex k A B P Q).X n
  | ⟨(_, 0), _⟩ => 0
  | ⟨(_, 1), _⟩ => 0
  | ⟨(_, 2), _⟩ => 0
  | ⟨(i, j+3), h⟩ => (cubicInsert k A B P Q n ⟨(i,j), by omega⟩).comp
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r j).hom)

def firstCubic (n : ℕ) : (complex k A B P Q).X (n+3) →ₗ[E] (complex k A B P Q).X n :=
  (DFinsupp.coprodMap (firstCubicEntry k A B P Q p n)).comp
    (termDirectSumEquiv k A B P Q (n+3)).toLinearMap

def secondCubic (n : ℕ) : (complex k A B P Q).X (n+3) →ₗ[E] (complex k A B P Q).X n :=
  (DFinsupp.coprodMap (secondCubicEntry k A B P Q r n)).comp
    (termDirectSumEquiv k A B P Q (n+3)).toLinearMap

@[simp] theorem firstCubic_insert (n : ℕ) (ij : Diagonal (n+3))
    (x : summands k A B P Q (n+3) ij) :
    firstCubic k A B P Q p n (cubicInsert k A B P Q (n+3) ij x) =
      firstCubicEntry k A B P Q p n ij x := by
  simp [firstCubic, cubicInsert, DFinsupp.coprodMap_apply_single]

@[simp] theorem secondCubic_insert (n : ℕ) (ij : Diagonal (n+3))
    (x : summands k A B P Q (n+3) ij) :
    secondCubic k A B P Q r n (cubicInsert k A B P Q (n+3) ij x) =
      secondCubicEntry k A B P Q r n ij x := by
  simp [secondCubic, cubicInsert, DFinsupp.coprodMap_apply_single]

end ArExplicit.ExternalTensor

end

end OAI
