import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelVelocityRecurrence
import OAI.NumberTheory.DukePrimeDegree.Geometry.ComponentRootConstancy

namespace OAI

/-!
# Root recovery from finitely many diagonal recurrence statements

For each root, a single diagonal has that root as its unique largest
weight. Stability under this one diagonal gives stability under all its
positive integer powers, which is enough to project onto that root.
Thus the actual component application requires only finitely many
recurrence statements, rather than a simultaneous assertion for an
uncountable family of diagonal elements.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_pow_mem {n : ℕ}
    (W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) (a : G n)
    (hW : ∀ V ∈ W, slMatrixConjugation a V ∈ W)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ W) (m : ℕ) :
    slMatrixConjugation (a ^ m) V ∈ W := by
  induction m with
  | zero => simpa only [pow_zero, slMatrixConjugation_one] using hV
  | succ m hm =>
    rw [pow_succ, slMatrixConjugation_mul]
    exact hW _ hm

theorem single_mem_of_isolating_diagonal_stability {n : ℕ}
    (W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (i j : Fin n) (hij : i ≠ j)
    (hW : ∀ V ∈ W,
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) 1).val * V *
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) (-1)).val ∈ W)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ W) :
    Matrix.single i j (V i j) ∈ W := by
  let ell := rootIsolationWeights i j
  have hell := rootIsolationWeights_sum i j
  let a := diagonalOneParameter ell hell (-1)
  have hstep : ∀ U ∈ W, slMatrixConjugation a U ∈ W := by
    intro U hU
    simpa only [a, slMatrixConjugation, diagonalOneParameter_neg, inv_inv] using hW U hU
  have hpower (m : ℕ) :
      (diagonalOneParameter ell hell (m : ℝ)).val * V *
        (diagonalOneParameter ell hell (-(m : ℝ))).val ∈ W := by
    have hm := slMatrixConjugation_pow_mem W a hstep hV m
    simpa only [a, slMatrixConjugation, diagonalOneParameter_neg,
      diagonalOneParameter_nat, inv_pow, inv_inv] using hm
  apply W.closed_of_finiteDimensional.mem_of_tendsto
    (tendsto_diagonal_matrix_root_projection i j hij V)
  exact Eventually.of_forall fun m => W.smul_mem _ (hpower m)

theorem full_root_of_isolating_diagonal_velocity {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (i j : Fin n) (hij : i ≠ j)
    (hW : ∀ V ∈ matrixVelocitySpace L,
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) 1).val * V *
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) (-1)).val ∈ matrixVelocitySpace L)
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace L) (hijV : V i j ≠ 0) :
    ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L := by
  have hs := single_mem_of_isolating_diagonal_stability (matrixVelocitySpace L) i j hij hW hV
  apply (root_direction_mem_velocitySpace_iff hij L hclosed).mp
  have hscale := (matrixVelocitySpace L).smul_mem (V i j)⁻¹ hs
  have he : (V i j)⁻¹ • Matrix.single i j (V i j) = Matrix.single i j (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hijV]
  rwa [he] at hscale

/-- Conditioning on a subgroup normalized by the diagonal action cannot
introduce velocity coefficients outside the ambient invariant-root
pattern. This applies in particular to a single coordinate block; the
individual conditional measures need not be diagonal invariant. -/
theorem ae_normalized_component_velocity_support
    (d : ℕ) (H : Subgroup (G (d + 1)))
    (hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X (d + 1))) z)),
      ∀ i j, ¬rootInvarianceRelation μ i j → V i j = 0 := by
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H (X (d + 1))
  have hdiag (i j : Fin (d + 1)) : ∀ᵐ z ∂μ.trim hm,
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup (condExpKernel μ m z)),
        (diagonalOneParameter (rootIsolationWeights i j)
          (rootIsolationWeights_sum i j) 1).val * V *
        (diagonalOneParameter (rootIsolationWeights i j)
          (rootIsolationWeights_sum i j) (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup (condExpKernel μ m z)) := by
    let ell := rootIsolationWeights i j
    have hell := rootIsolationWeights_sum i j
    have hpres : μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = μ := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact (measurePreserving_smul
        (Multiplicative.ofAdd (fun k : Fin d => ell k.castSucc * (-1))) μ).map_eq
    have hnormal : diagonalOneParameter ell hell (-1) ∈
        Subgroup.normalizer (H : Set (G (d + 1))) := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hAH _
    exact ae_conditional_velocity_diagonal_stable H μ ell hell hnormal hpres
  have hno (i j : Fin (d + 1)) : ∀ᵐ z ∂μ.trim hm, ∀ hij : i ≠ j,
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
        invariantRightSubgroup (condExpKernel μ m z)) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · exact (ae_component_root_implies_ambient_root d H hAH μ hij).mono fun _ hz _ => hz
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hdiag i)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hno i))] with z hz hroot
  intro V hV i j hn
  by_contra hne
  have hij : i ≠ j := fun he => hn (Or.inl he)
  have hfull := full_root_of_isolating_diagonal_velocity
    (invariantRightSubgroup (condExpKernel μ m z))
    (isClosed_invariantRightSubgroup _) i j hij (hz i j) hV hne
  exact hn (Or.inr ⟨hij, hroot i j hij hfull⟩)

/-- The actual root-generated conditional measures have the required
velocity support by the explicit diagonal normalization of their group. -/
theorem ae_rootGenerated_component_velocity_support
    (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le (invariantRootGeneratedGroup μ) (X (d + 1))),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma (invariantRootGeneratedGroup μ) (X (d + 1))) z)),
      ∀ i j, ¬rootInvarianceRelation μ i j → V i j = 0 := by
  apply ae_normalized_component_velocity_support d (invariantRootGeneratedGroup μ) ?_ μ
  intro u
  let ell : Fin (d + 1) → ℝ := Fin.snoc u (-∑ k, u k)
  have hell : ∑ k, ell k = 0 := by simp [ell, Fin.sum_univ_castSucc]
  have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext k
    simp [ell]
  rw [← ha]
  exact diagonal_normalizes_rootGeneratedGroup μ ell hell 1

end DukePrimeDegree

end

end OAI
