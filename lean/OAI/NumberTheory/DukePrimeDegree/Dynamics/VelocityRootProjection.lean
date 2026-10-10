import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootVelocityRecovery
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup

namespace OAI

/-!
# Root projection inside an invariant velocity space

The extreme weight of a split diagonal isolates an off-diagonal matrix
coefficient inside a closed invariant vector space. For the actual
velocity space of a closed measure stabilizer, the isolated direction
then gives an actual full real root group by the power approximation.
This is the linear step after, rather than a substitute for, proving
diagonal invariance of the component velocity spaces by recurrence.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonal_matrix_conjugation_entry {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ a, ell a = 0) (t : ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((diagonalOneParameter ell hell t).val * V *
      (diagonalOneParameter ell hell (-t)).val) i j =
        Real.exp ((ell i - ell j) * t) * V i j := by
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * V *
    Matrix.diagonal (fun i => Real.exp (ell i * (-t)))) i j = _
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_assoc, mul_comm (V i j), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_diagonal_matrix_root_projection {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (V : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun m : ℕ => Real.exp (-2 * (m : ℝ)) •
      ((diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
        (m : ℝ)).val * V *
       (diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
        (-(m : ℝ))).val)) atTop (𝓝 (Matrix.single i j (V i j))) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have he (m : ℕ) :
      (Real.exp (-2 * (m : ℝ)) •
        ((diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
          (m : ℝ)).val * V *
         (diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
          (-(m : ℝ))).val)) a b =
      Real.exp ((rootIsolationWeights i j a - rootIsolationWeights i j b - 2) * (m : ℝ)) *
        V a b := by
    rw [Matrix.smul_apply, diagonal_matrix_conjugation_entry]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  by_cases hab : a = i ∧ b = j
  · obtain ⟨hai, hbj⟩ := hab
    subst a
    subst b
    simp only [rootIsolationWeights_peak i j hij, sub_self, zero_mul,
      Real.exp_zero, one_mul, Matrix.single_apply, and_self, ite_true]
    exact tendsto_const_nhds
  · have hc : rootIsolationWeights i j a - rootIsolationWeights i j b - 2 < 0 :=
      sub_neg.mpr (rootIsolationWeights_lt_peak i j hij a b hab)
    have hlim := (Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)).mul_const (V a b)
    have hab' : ¬ (i = a ∧ j = b) := by
      rintro ⟨hia, hjb⟩
      exact hab ⟨hia.symm, hjb.symm⟩
    simpa only [Function.comp_def, zero_mul, Matrix.single_apply, ite_eq_right hab'] using hlim

/-- Closedness is automatic for finite-dimensional real submodules.
Every off-diagonal coefficient projects to a pure root direction. -/
theorem single_mem_of_diagonal_invariant_submodule {n : ℕ}
    (W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hW : ∀ (ell : Fin n → ℝ) (hell : ∑ a, ell a = 0) (t : ℝ),
      ∀ V ∈ W, (diagonalOneParameter ell hell t).val * V *
        (diagonalOneParameter ell hell (-t)).val ∈ W)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ W)
    (i j : Fin n) (hij : i ≠ j) : Matrix.single i j (V i j) ∈ W := by
  apply W.closed_of_finiteDimensional.mem_of_tendsto
    (tendsto_diagonal_matrix_root_projection i j hij V)
  exact Eventually.of_forall fun m => W.smul_mem _
    (hW (rootIsolationWeights i j) (rootIsolationWeights_sum i j) m V hV)

/-- Diagonal invariance of the subgroup velocity space projects every
nonzero off-diagonal velocity onto a full invariant root group. -/
theorem full_root_of_nonzero_component_velocity {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hW : ∀ (ell : Fin n → ℝ) (hell : ∑ a, ell a = 0) (t : ℝ),
      ∀ V ∈ matrixVelocitySpace L, (diagonalOneParameter ell hell t).val * V *
        (diagonalOneParameter ell hell (-t)).val ∈ matrixVelocitySpace L)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ matrixVelocitySpace L)
    (i j : Fin n) (hij : i ≠ j) (hijV : V i j ≠ 0) :
    ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L := by
  have hs := single_mem_of_diagonal_invariant_submodule (matrixVelocitySpace L) hW hV i j hij
  apply (root_direction_mem_velocitySpace_iff hij L hclosed).mp
  have hscale := (matrixVelocitySpace L).smul_mem (V i j)⁻¹ hs
  have he : (V i j)⁻¹ • Matrix.single i j (V i j) = Matrix.single i j (1 : ℝ) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp only [inv_mul_cancel₀ hijV, mul_zero]
  rwa [he] at hscale

theorem velocity_cross_entry_zero_of_no_new_roots {n : ℕ}
    (ν μ : Measure (X n)) [IsFiniteMeasure ν]
    (r : Setoid (Fin n))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hW : ∀ (ell : Fin n → ℝ) (hell : ∑ a, ell a = 0) (t : ℝ),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup ν),
        (diagonalOneParameter ell hell t).val * V *
          (diagonalOneParameter ell hell (-t)).val ∈
            matrixVelocitySpace (invariantRightSubgroup ν))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j),
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup ν) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ)
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace (invariantRightSubgroup ν))
    (i j : Fin n) (hnr : ¬r i j) : V i j = 0 := by
  by_contra hne
  have hij : i ≠ j := by
    intro he
    subst j
    exact hnr (r.refl i)
  have hu := full_root_of_nonzero_component_velocity (invariantRightSubgroup ν)
    (isClosed_invariantRightSubgroup ν) hW hV i j hij hne
  exact hnr ((hr i j).mpr (Or.inr ⟨hij, hroot i j hij hu⟩))

end DukePrimeDegree

end

end OAI
