import Mathlib
import OAI.Analysis.Commutator.SeparableTestGeometry

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (h : ℕ)
  (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)

include hX

lemma bound_on_vector {c : ℝ} (hc : 0≤c) (ξ : PiLp 2 (fun _ : Fin h => H))
    (hb : ‖diagonalAmplification h (restrictedY h X Y ξ)*
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
      diagonalAmplification h (restrictedY h X Y ξ)‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range)
        (restrictedY h X Y ξ)*
      ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖) :
    ‖(diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y) ξ‖≤
      (c*commutatorSeminorm P Y*‖matrixOperator h X‖)*‖ξ‖ := by
  let σ := representation h X Y ξ
  let Z := restrictedY h X Y ξ
  let X₀ := fun i j => σ (entries h X i j)
  have hb' : ‖diagonalAmplification h Z*matrixOperator h X₀-
      matrixOperator h X₀*diagonalAmplification h Z‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
    hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left (seminorm_bound h X Y ξ P hX) hc)
      (matrix_norm_le h X Y ξ) (norm_nonneg (matrixOperator h X₀))
      (mul_nonneg hc (commutatorSeminorm_nonneg P Y)))
  rw [commutator_vector h X Y ξ,LinearIsometry.norm_map]
  exact ((diagonalAmplification h Z*matrixOperator h X₀-
    matrixOperator h X₀*diagonalAmplification h Z).le_opNorm (vector h X Y ξ)).trans
      (by rw [vector_norm]; exact mul_le_mul_of_nonneg_right hb' (norm_nonneg ξ))

def SeparableBound (c : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (h : ℕ),1≤h →
    ∀ X : Matrix (Fin h) (Fin h) (K →L[ℂ] K), (∀ i j,X i j∈P) →
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖

omit hX in
lemma SeparableBound.on_range {c : ℝ} (hsep : SeparableBound.{u} c)
    {A K : Type u} [CStarAlgebra A] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Z : K →L[ℂ] K) (h : ℕ) (hh : 1≤h)
    (W : Matrix (Fin h) (Fin h) A) :
    ‖diagonalAmplification h Z*matrixOperator h (fun i j => σ (W i j))-
      matrixOperator h (fun i j => σ (W i j))*diagonalAmplification h Z‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant σ.range) Z*
        ‖matrixOperator h (fun i j => σ (W i j))‖ := by
  apply hsep K _ Z h hh
  intro i j
  exact NormalGNS.subset_bicommutant σ.range ⟨W i j,rfl⟩

omit hX in
lemma restricted_bound {c : ℝ} (hsep : SeparableBound.{u} c) (hh : 1≤h)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    ‖diagonalAmplification h (restrictedY h X Y ξ)*
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
      diagonalAmplification h (restrictedY h X Y ξ)‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range)
        (restrictedY h X Y ξ)*
      ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖ := by
  exact hsep.on_range (representation h X Y ξ) (restrictedY h X Y ξ) h hh (entries h X)

theorem bound_of_separable_bound {c : ℝ} (hc : 0≤c)
    (hsep : SeparableBound.{u} c) (hh : 1≤h) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hc (commutatorSeminorm_nonneg P Y)) (norm_nonneg _))
  intro ξ
  exact bound_on_vector P Y h X hX hc ξ (restricted_bound Y h X hsep hh ξ)

end Kadison.SeparableTest

end

end
end

end OAI
