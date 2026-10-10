import OAI.Analysis.BoundedHochschild.MatrixRightAveraging
import OAI.Analysis.BoundedHochschild.MinimalRightAverages

namespace OAI

/-! The compact averaging family retains its complete bound. Matrix
reconstruction converts the relevant norm balls to closed weak-star conditions. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma rightAverageOrbit_completelyBounded (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) {S : M →L[ℂ] M}
    (hS : S ∈ rightAverageOrbit T) : CompletelyBoundedEstimate S C := by
  obtain ⟨n, m, hm, rfl⟩ := hS
  cases n with
  | zero =>
      have heq : finiteRightAverage m T = 0 := by
        ext a
        simp only [finiteRightAverage_apply, Fin.sum_univ_zero, zero_apply]
      rw [heq]
      refine ⟨hT.1, fun k A => ?_⟩
      have hz : A.map (0 : M →L[ℂ] M) = 0 := by ext; rfl
      rw [hz, norm_zero]
      exact mul_nonneg hT.1 (norm_nonneg _)
  | succ n => exact finiteRightAverage_completelyBounded e hno m hm T hT

/-- Reconstruct a matrix of weak-dual values in the original algebra. -/
def weakMatrixReconstruction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (c : Fin n → PartialIso M) (A : CStarMatrix (Fin n) (Fin n) M)
    (F : M → WeakDual ℂ X) : WeakDual ℂ X :=
  ∑ i, ∑ j, weakDualOperator e ((ContinuousLinearMap.mul ℂ M).flip (star (c j : M)))
    (weakDualOperator e (ContinuousLinearMap.mul ℂ M (c i : M)) (F (A i j)))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakMatrixReconstruction_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (c : Fin n → PartialIso M) (A : CStarMatrix (Fin n) (Fin n) M) (T : M →L[ℂ] M) :
    weakMatrixReconstruction e c A (weakOperatorImage e T) =
      StrongDual.toWeakDual (e.symm (columnReconstruction c (A.map T))) := by
  simp only [weakMatrixReconstruction, weakOperatorImage, weakDualOperator_image,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', columnReconstruction,
    CStarMatrix.map_apply, map_sum]

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakMatrixReconstruction_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (c : Fin n → PartialIso M) (A : CStarMatrix (Fin n) (Fin n) M) :
    Continuous (weakMatrixReconstruction e c A) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).2 (star (c j : M)))).comp
    ((weakDualOperator_continuous e _
      ((HochschildSakai.abstract_multiplication_normal e).1 (c i : M))).comp
        (continuous_apply (A i j)))

lemma columnReconstruction_norm {n : ℕ} (c : Fin n → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (A : CStarMatrix (Fin n) (Fin n) M) :
    ‖columnReconstruction c A‖ = ‖A‖ := by
  rw [← columnCompression_norm c hi ho hs (columnReconstruction c A),
    columnCompression_reconstruction c hi ho]

/-- Every realized member of the weak-star closed averaging orbit has the
same complete bound as the original map. -/
theorem weakRightAverageOrbit_completelyBounded (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) (S : M →L[ℂ] M)
    (hS : weakOperatorImage e S ∈ weakRightAverageOrbit e T) :
    CompletelyBoundedEstimate S C := by
  refine ⟨hT.1, ?_⟩
  intro k A
  cases k with
  | zero =>
      have hz : A = 0 := by ext i j; exact Fin.elim0 i
      have hm : A.map S = 0 := by ext i j; exact Fin.elim0 i
      rw [hm, hz, norm_zero, mul_zero]
  | succ k =>
      obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno (k + 1)
      have hclosed : IsClosed {F : M → WeakDual ℂ X |
          ‖WeakDual.toStrongDual (weakMatrixReconstruction e c A F)‖ ≤ C * ‖A‖} := by
        have h := (WeakDual.isClosed_closedBall (0 : StrongDual ℂ X) (C * ‖A‖)).preimage
          (weakMatrixReconstruction_continuous e c A)
        convert h using 1
        ext F
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hsub : weakOperatorImage e '' rightAverageOrbit T ⊆
          {F | ‖WeakDual.toStrongDual (weakMatrixReconstruction e c A F)‖ ≤ C * ‖A‖} := by
        rintro F ⟨U, hU, rfl⟩
        change ‖WeakDual.toStrongDual (weakMatrixReconstruction e c A (weakOperatorImage e U))‖ ≤ _
        rw [weakMatrixReconstruction_image]
        change ‖e.symm (columnReconstruction c (A.map U))‖ ≤ _
        rw [e.symm.norm_map, columnReconstruction_norm c hi ho hs]
        exact (rightAverageOrbit_completelyBounded e hno T hT hU).2 (k + 1) A
      have hb := closure_minimal hsub hclosed hS
      change ‖WeakDual.toStrongDual (weakMatrixReconstruction e c A (weakOperatorImage e S))‖ ≤ _ at hb
      rw [weakMatrixReconstruction_image] at hb
      change ‖e.symm (columnReconstruction c (A.map S))‖ ≤ _ at hb
      rwa [e.symm.norm_map, columnReconstruction_norm c hi ho hs] at hb

end BoundedHochschild.KadisonRingrose

end

end OAI
