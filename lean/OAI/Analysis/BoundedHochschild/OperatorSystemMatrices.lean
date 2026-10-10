import OAI.Analysis.BoundedHochschild.OperatorSystemExtension
import OAI.Analysis.BoundedHochschild.StinespringBounds

namespace OAI

/-! The scalar matrix functional used in finite-dimensional positive extension. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSystemMatrices (S : Submodule ℂ A) (n : ℕ) :
    Submodule ℂ (CStarMatrix (Fin n) (Fin n) A) where
  carrier := {X | ∀ i j, X i j ∈ S}
  zero_mem' := fun _ _ => S.zero_mem
  add_mem' hX hY := fun i j => S.add_mem (hX i j) (hY i j)
  smul_mem' z _X hX := fun i j => S.smul_mem z (hX i j)

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrices_one (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) (n : ℕ) :
    (1 : CStarMatrix (Fin n) (Fin n) A) ∈ operatorSystemMatrices S n := by
  intro i j
  change (if i = j then (1 : A) else 0) ∈ S
  split_ifs
  · exact h1
  · exact S.zero_mem

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrices_star (S : Submodule ℂ A)
    (hs : ∀ a ∈ S, star a ∈ S) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : X ∈ operatorSystemMatrices S n) :
    star X ∈ operatorSystemMatrices S n := fun i j => hs _ (hX j i)

def operatorSystemAmplification {B : Type*} [CStarAlgebra B]
    (S : Submodule ℂ A) (φ : S →ₗ[ℂ] B) (n : ℕ) :
    operatorSystemMatrices S n →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B where
  toFun X := CStarMatrix.ofMatrix (fun i j => φ ⟨X.val i j, X.property i j⟩)
  map_add' X Y := by
    apply CStarMatrix.ext
    intro i j
    exact map_add φ ⟨X.val i j, X.property i j⟩ ⟨Y.val i j, Y.property i j⟩
  map_smul' z X := by
    apply CStarMatrix.ext
    intro i j
    exact map_smul φ z ⟨X.val i j, X.property i j⟩

def operatorSystemMatrixFunctional (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    {n : ℕ} (ξ : Fin n → H) : operatorSystemMatrices S n →ₗ[ℂ] ℂ :=
  (operatorMatrixVectorFunctional ξ).toLinearMap.comp (operatorSystemAmplification S φ n)

lemma operatorSystemMatrixFunctional_nonneg
    (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H)) {n : ℕ} (ξ : Fin n → H)
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X)
    (X : operatorSystemMatrices S n) (hX : 0 ≤ (X : CStarMatrix (Fin n) (Fin n) A)) :
    0 ≤ operatorSystemMatrixFunctional S φ ξ X :=
  (operatorMatrixVectorFunctional ξ).map_nonneg (hφ X hX)

end BoundedHochschild.KadisonRingrose

end

end OAI
