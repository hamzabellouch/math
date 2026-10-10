import OAI.Analysis.BoundedHochschild.OperatorSystemMatrices
import OAI.Analysis.BoundedHochschild.CompletelyPositiveCompression

namespace OAI

/-! Compression of positive matrix levels on a unital linear subspace. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compressOperatorSystem (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) : S →ₗ[ℂ] (K →L[ℂ] K) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma compressOperatorSystem_positive (S : Submodule ℂ A)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H) {n : ℕ}
    (X : operatorSystemMatrices S n) (hX : 0 ≤ operatorSystemAmplification S φ n X) :
    0 ≤ operatorSystemAmplification S (compressOperatorSystem S φ V) n X := by
  apply operatorMatrix_nonneg_of_quadratic
  intro ξ
  change 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i)
    (V.adjoint (φ ⟨X.val i j, X.property i j⟩ (V (ξ j))))
  simp only [ContinuousLinearMap.adjoint_inner_right]
  exact operatorMatrix_quadratic_nonneg (operatorSystemAmplification S φ n X) hX
    (fun i => V (ξ i))

omit [PartialOrder A] [StarOrderedRing A] in
lemma compressOperatorSystem_one (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (hφ : φ ⟨1, h1⟩ = 1) (V : K →ₗᵢ[ℂ] H) :
    compressOperatorSystem S φ V.toContinuousLinearMap ⟨1, h1⟩ = 1 := by
  change V.toContinuousLinearMap.adjoint.comp ((φ ⟨1, h1⟩).comp V.toContinuousLinearMap) = 1
  rw [hφ]
  change V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap = 1
  exact V.adjoint_comp_self

end BoundedHochschild.KadisonRingrose

end

end OAI
