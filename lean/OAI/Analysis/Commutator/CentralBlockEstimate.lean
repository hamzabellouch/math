import Mathlib
import OAI.Analysis.Commutator.CentralCorner
import OAI.Analysis.Commutator.SeparableFactorMain

namespace OAI

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CentralCorner

open ConcreteCorner MatrixCornerHilbert ReducingRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) {p : M} (hp : IsStarProjection p)
    (hz : (p:H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)))

omit [TopologicalSpace.SeparableSpace H] in
lemma invariant_of_commute (Y : H →L[ℂ] H) (hy : Y*(p:H →L[ℂ] H)=(p:H →L[ℂ] H)*Y) :
    ∀ x∈Space hp,Y x∈Space hp := by
  intro x hx
  rw [mem_fixedSpace] at hx ⊢
  change (p:H →L[ℂ] H) x=x at hx
  change (p:H →L[ℂ] H) (Y x)=Y x
  exact (congrArg (fun operator : H →L[ℂ] H => operator x) hy.symm).trans (congrArg Y hx)

include hz in
lemma corner_matrix_bound
    (hmin : AtomicFactor.IsMinimalProjection (center M) (p:H →L[ℂ] H))
    (Y : H →L[ℂ] H) (hY : ∀ x∈Space hp,Y x∈Space hp)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) M) :
    ‖diagonalAmplification h (Y.restrict hY)*matrixOperator h (fun i j => restriction M hp hz (X i j))-
      matrixOperator h (fun i j => restriction M hp hz (X i j))*diagonalAmplification h (Y.restrict hY)‖≤
    3122*commutatorSeminorm M Y*‖matrixOperator h (fun i j => (X i j:H →L[ℂ] H))‖ := by
  have hX (i j : Fin h) : restriction M hp hz (X i j)∈vonNeumann hp := by
    change restriction M hp hz (X i j)∈(vonNeumann hp).toStarSubalgebra
    rw [←restriction_range M hp hz]
    exact Set.mem_range_self (X i j)
  have hb := uniform_commutator_separable_factor (vonNeumann hp)
    (factor_of_minimal_center M hp hz hmin) (Y.restrict hY) h hh
    (fun i j => restriction M hp hz (X i j)) hX
  have hn := restricted_matrix_norm_le M.toStarSubalgebra.subtype (Space hp)
    (invariant M hp hz) h X
  have hg := seminorm_le M hp hz Y hY
  exact hb.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hg (by norm_num))
    (norm_nonneg (matrixOperator h (fun i j => restriction M hp hz (X i j))))).trans
      (mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y))))

include hp hz in
lemma projected_vector_bound
    (hmin : AtomicFactor.IsMinimalProjection (center M) (p:H →L[ℂ] H))
    (Y : H →L[ℂ] H) (hy : Y*(p:H →L[ℂ] H)=(p:H →L[ℂ] H)*Y)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) M)
    (ξ : PiLp 2 fun _ : Fin h => H) :
    ‖(diagonalAmplification h Y*matrixOperator h (fun i j => (X i j:H →L[ℂ] H))-
      matrixOperator h (fun i j => (X i j:H →L[ℂ] H))*diagonalAmplification h Y)
        (diagonalAmplification h (p:H →L[ℂ] H) ξ)‖≤
    (3122*commutatorSeminorm M Y*‖matrixOperator h (fun i j => (X i j:H →L[ℂ] H))‖)*
      ‖diagonalAmplification h (p:H →L[ℂ] H) ξ‖ := by
  let K := Space hp
  let hy' := invariant_of_commute M hp Y hy
  let η : PiLp 2 fun _ : Fin h => K := WithLp.toLp 2 (fun i => project hp (ξ i))
  have heη : diagonalAmplification h (p:H →L[ℂ] H) ξ=matrixInclusion K h η := by
    ext i
    rfl
  have he := congrArg (fun T => T η) (matrix_commutator_intertwines
    M.toStarSubalgebra.subtype K (invariant M hp hz) Y hy' h X)
  change (diagonalAmplification h Y*matrixOperator h (fun i j => (X i j:H →L[ℂ] H))-
      matrixOperator h (fun i j => (X i j:H →L[ℂ] H))*diagonalAmplification h Y)
        (matrixInclusion K h η)=matrixInclusion K h
    ((diagonalAmplification h (Y.restrict hy')*matrixOperator h (fun i j => restriction M hp hz (X i j))-
      matrixOperator h (fun i j => restriction M hp hz (X i j))*diagonalAmplification h (Y.restrict hy')) η) at he
  rw [heη,he,(matrixInclusion K h).norm_map,(matrixInclusion K h).norm_map]
  exact (ContinuousLinearMap.le_opNorm _ η).trans (mul_le_mul_of_nonneg_right
    (corner_matrix_bound M hp hz hmin Y hy' h hh X) (norm_nonneg η))

end Kadison.CentralCorner
end
end

end OAI
