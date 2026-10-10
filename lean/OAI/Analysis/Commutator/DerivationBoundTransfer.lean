import Mathlib
import OAI.Analysis.Commutator.DerivationKaplansky
import OAI.Analysis.Commutator.DerivationMatrixColumns
import OAI.Analysis.Commutator.MatrixReindexBound

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

namespace Kadison.DerivationColumns

open CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (D : A →L[ℂ] (H →L[ℂ] H))
  (hD : ∀ a b,D (a*b)=(D a).comp (σ b)+(σ a).comp (D b))

include hD in
theorem matrix_bound_of_bicommutant_bound {c : ℝ} (hc : 0≤c)
    (hP : ∀ (Y : H →L[ℂ] H) (h : ℕ),1≤h →
      ∀ X : Matrix (Fin h) (Fin h) (H →L[ℂ] H),
      (∀ i j,X i j∈NormalGNS.bicommutant σ.range) →
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant σ.range) Y*‖matrixOperator h X‖)
    {ι : Type*} [Fintype ι] (X : CStarMatrix ι ι A) :
    ‖matrixAction (fun i j => D (X i j))‖≤c*‖D‖*‖X‖ := by
  classical
  obtain ⟨Q⟩ := CyclicDecomposition.exists_decomposition σ.range
  apply matrix_bound_of_fin D (mul_nonneg hc (norm_nonneg D)) ?_ X
  intro h hh X
  apply norm_le_of_finite_columns σ Q h _ (mul_nonneg (mul_nonneg hc (norm_nonneg D)) (norm_nonneg X))
  intro s
  rw [←finite_matrix_identity σ D hD Q s h X]
  have hXm : ∀ i j,σ (X i j)∈NormalGNS.bicommutant σ.range := fun i j =>
    NormalGNS.subset_bicommutant σ.range (Set.mem_range_self (X i j))
  have hb := hP (finiteImplementer σ D hD Q s) h hh (fun i j => σ (X i j)) hXm
  change ‖diagonalAmplification h (finiteImplementer σ D hD Q s)*matrixRepresentation σ X-
      matrixRepresentation σ X*diagonalAmplification h (finiteImplementer σ D hD Q s)‖≤
    c*commutatorSeminorm (NormalGNS.bicommutant σ.range) (finiteImplementer σ D hD Q s)*‖matrixRepresentation σ X‖ at hb
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (finite_seminorm_bound σ D hD Q s) hc)
    (matrixRepresentation_norm_le σ X) (norm_nonneg _) (mul_nonneg hc (norm_nonneg D)))

include hD in
theorem implementation_of_bicommutant_bound {c : ℝ} (hc : 0≤c)
    (hP : ∀ (Y : H →L[ℂ] H) (h : ℕ),1≤h →
      ∀ X : Matrix (Fin h) (Fin h) (H →L[ℂ] H),
      (∀ i j,X i j∈NormalGNS.bicommutant σ.range) →
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant σ.range) Y*‖matrixOperator h X‖) :
    ∃ V : H →L[ℂ] H,‖V‖≤(1+c)^2*‖D‖ ∧ ∀ a : A,D a=V.comp (σ a)-(σ a).comp V :=
  CbFactor.rectangular_implementation_quantitative σ σ D hD hc
    (fun _ _ X => matrix_bound_of_bicommutant_bound σ D hD hc hP X)

end Kadison.DerivationColumns

end

end
end

end OAI
