import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.UnitLineRemainder
import OAI.Combinatorics.TriangleRemoval.Process.EigenProjector
import OAI.Combinatorics.TriangleRemoval.Process.EigenvalueAbsRowsum

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def normalizedOnes : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (Fintype.card ι : ℝ))⁻¹)

noncomputable def averagingProjector : Matrix ι ι ℝ :=
  fun _ _ => (Fintype.card ι : ℝ)⁻¹

omit [DecidableEq ι] in
theorem normalizedOnes_norm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ = 1 := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hnorm : ‖(normalizedOnes : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [normalizedOnes, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
    exact mul_inv_cancel₀ (ne_of_gt hn)
  nlinarith [norm_nonneg (normalizedOnes : EuclideanSpace ℝ ι)]

theorem normalizedOnes_residual (A : Matrix ι ι ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ≤ δ := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = Fintype.card ι :=
    Real.sq_sqrt (le_of_lt hn)
  have hcoords : ∀ i, ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes).ofLp i =
      ((∑ j, A i j) - 1) * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ := by
    intro i
    simp [normalizedOnes, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
      Finset.sum_mul, sub_mul]
  have hsq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes‖ ^ 2 ≤ δ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i, |((∑ j, A i j) - 1)| ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        simp only [hcoords, Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ∑ _ : ι, δ ^ 2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2) (sq_nonneg _)
      _ = δ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hs]
        field_simp
  nlinarith [norm_nonneg ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A normalizedOnes - normalizedOnes)]

omit [Nonempty ι] in
theorem eigenProjector_entry (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k i j : ι) :
    eigenProjector A hA k i j = hA.eigenvectorBasis k i * hA.eigenvectorBasis k j := by
  simp [eigenProjector, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Pi.single_apply]

omit [Nonempty ι] in
theorem eigenProjector_toCLM (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (eigenProjector A hA k) =
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k) := by
  ext x i
  change ((eigenProjector A hA k) *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    eigenProjector_entry, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Nonempty ι] in
theorem averagingProjector_toCLM :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (averagingProjector : Matrix ι ι ℝ) =
      rankOne ℝ (normalizedOnes : EuclideanSpace ℝ ι) normalizedOnes := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hn]
  ext x i
  change (averagingProjector *ᵥ x.ofLp) i = _
  simp only [rankOne_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    averagingProjector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    normalizedOnes]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  nlinarith [congrArg (fun t : ℝ => t * x.ofLp j) hs]

theorem star_approximation_from_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (δ θ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ)
    (hpos : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, |(∑ j, A i j) - 1| ≤ δ)
    (r : ℕ) (hr : Even r) (hr0 : r ≠ 0)
    (htrace : (A ^ r).trace ≤ (1 - δ) ^ r + θ ^ r) :
    ‖A - averagingProjector‖ ≤ 4 * θ + 7 * δ := by
  have hrlo : ∀ i, 1 - δ ≤ ∑ j, A i j := fun i => by
    have hh := (abs_le.mp (hrow i)).1
    linarith
  have hrhi : ∀ i, ∑ j, |A i j| ≤ 1 + δ := fun i => by
    simp_rw [abs_of_nonneg (hpos i _)]
    have hh := (abs_le.mp (hrow i)).2
    linarith
  obtain ⟨k, hklo, hkhi, _⟩ := exists_leading_of_rowsums A hA (1-δ) (1+δ)
    (by linarith) hrlo hrhi
  have hlam : |hA.eigenvalues k - 1| ≤ δ := by
    have hhi := (abs_le.mp hkhi).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htail := eigenvalue_tail_of_trace A hA k r hr hr0 (1-δ) θ
    (by linarith) hθ hklo htrace
  have happrox := eigenProjector_approximation A hA k θ hθ htail
  have heig : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A - hA.eigenvalues k •
      rankOne ℝ (hA.eigenvectorBasis k) (hA.eigenvectorBasis k)‖ ≤ θ := by
    rw [← eigenProjector_toCLM A hA k, ← map_smul, ← map_sub,
      Matrix.l2_opNorm_toEuclideanCLM]
    exact happrox
  have hfinal := projector_transfer ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A)
    (hA.eigenvectorBasis k) normalizedOnes (hA.eigenvectorBasis.norm_eq_one k)
    normalizedOnes_norm (hA.eigenvalues k) θ δ δ heig hlam
    (normalizedOnes_residual A δ hδ0 hrow)
  rw [← averagingProjector_toCLM, ← map_sub, Matrix.l2_opNorm_toEuclideanCLM] at hfinal
  linarith

end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
