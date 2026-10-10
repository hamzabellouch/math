import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockDiagonalAlgebra
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.MeasurableSpace

namespace OAI

/-!
# Finite measures in the matrix conjugation representation

This is the elementary recurrence part of the needed Borel-density
argument. A finite measure invariant under a strict real contraction is
concentrated at zero. Applied to matrix coefficients, split diagonal
conjugation forces invariant finite matrix measures onto diagonal matrices.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree

theorem ae_zero_of_mul_map_eq (ν : Measure ℝ) [IsFiniteMeasure ν]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hmap : ν.map (fun x => c * x) = ν) : ∀ᵐ x ∂ν, x = 0 := by
  let f : ℝ → ℝ := fun x => c * x
  have hf : MeasurePreserving f ν ν := ⟨by fun_prop, hmap⟩
  have hlim (x : ℝ) : Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 0) := by
    have hit (n : ℕ) : f^[n] x = c ^ n * x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        simp only [f, pow_succ]
        ring
    simpa only [hit, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const x
  filter_upwards [hf.conservative.ae_frequently_mem_of_mem_nhds] with x hx
  by_contra hne
  obtain ⟨U, V, hU, hV, hdisj⟩ := t2_separation_nhds hne
  have hrec := hx U hU
  have hev := (hlim x).eventually hV
  obtain ⟨n, hnU, hnV⟩ := (hrec.and_eventually hev).exists
  exact Set.disjoint_left.mp hdisj hnU hnV

/-- Conjugation by the split real diagonal one-parameter subgroup. -/
def diagonalMatrixConjugation {n : ℕ} (ell : Fin n → ℝ) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => Real.exp (ell i * t)) * M *
    Matrix.diagonal (fun i => Real.exp (-ell i * t))

lemma diagonalMatrixConjugation_entry {n : ℕ} (ell : Fin n → ℝ) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    diagonalMatrixConjugation ell t M i j = Real.exp ((ell i - ell j) * t) * M i j := by
  simp only [diagonalMatrixConjugation, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, ← Real.exp_add]
  congr 2
  ring

lemma continuous_diagonalMatrixConjugation {n : ℕ} (ell : Fin n → ℝ) (t : ℝ) :
    Continuous (diagonalMatrixConjugation ell t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ =>
      Real.exp ((ell i - ell j) * t) * M i j) := by fun_prop
  simpa only [diagonalMatrixConjugation_entry] using hc

/-- Split diagonal invariance annihilates every nonzero weight. -/
theorem ae_matrix_entry_zero_of_split_invariance {n : ℕ}
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ)
    (hdiag : ∀ t : ℝ, μ.map (diagonalMatrixConjugation ell t) = μ)
    (i j : Fin n) (hij : ell i ≠ ell j) : ∀ᵐ M ∂μ, M i j = 0 := by
  let coord : Matrix (Fin n) (Fin n) ℝ → ℝ := fun M => M i j
  let t := -(ell i - ell j)
  let c := Real.exp ((ell i - ell j) * t)
  have hcoord : Measurable coord := by fun_prop
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hc1 : c < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hd : ell i - ell j ≠ 0 := sub_ne_zero.mpr hij
    dsimp [t]
    nlinarith [sq_pos_of_ne_zero hd]
  have hmap : (μ.map coord).map (fun x => c * x) = μ.map coord := by
    calc
      _ = μ.map (coord ∘ diagonalMatrixConjugation ell t) := by
        rw [Measure.map_map (by fun_prop) hcoord]
        congr 1
        funext M
        exact (diagonalMatrixConjugation_entry ell t M i j).symm
      _ = (μ.map (diagonalMatrixConjugation ell t)).map coord :=
        (Measure.map_map hcoord (continuous_diagonalMatrixConjugation ell t).measurable).symm
      _ = μ.map coord := by rw [hdiag t]
  exact ae_of_ae_map hcoord.aemeasurable (ae_zero_of_mul_map_eq (μ.map coord) c hc0 hc1 hmap)

/-- For a regular split diagonal subgroup, an invariant finite matrix
measure is supported on the diagonal matrix space. -/
theorem ae_diagonal_of_split_invariance {n : ℕ}
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, μ.map (diagonalMatrixConjugation ell t) = μ) :
    ∀ᵐ M ∂μ, M = Matrix.diagonal (fun i => M i i) := by
  have H : ∀ᵐ M ∂μ, ∀ i j, i ≠ j → M i j = 0 := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · exact (ae_matrix_entry_zero_of_split_invariance μ ell hdiag i j
        (fun he => hij (hell he))).mono (fun _ h _ => h)
  filter_upwards [H] with M hM
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [hM i j hij, Matrix.diagonal_apply_ne _ hij]

/-- Conjugation by a root unipotent matrix. -/
def rootMatrixConjugation {n : ℕ} (i j : Fin n) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.transvection i j t * M * Matrix.transvection i j (-t)

lemma continuous_rootMatrixConjugation {n : ℕ} (i j : Fin n) (t : ℝ) :
    Continuous (rootMatrixConjugation i j t) := by
  unfold rootMatrixConjugation
  fun_prop

/-- Once the matrix measure is diagonal, one invariant root forces the
two corresponding diagonal entries to coincide. -/
theorem ae_diagonal_entries_eq_of_root_invariance {n : ℕ}
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ))
    (hD : ∀ᵐ M ∂μ, M = Matrix.diagonal (fun i => M i i))
    (i j : Fin n) (hij : i ≠ j)
    (hroot : μ.map (rootMatrixConjugation i j 1) = μ) :
    ∀ᵐ M ∂μ, M i i = M j j := by
  have hDT : ∀ᵐ M ∂μ, rootMatrixConjugation i j 1 M =
      Matrix.diagonal (fun k => rootMatrixConjugation i j 1 M k k) := by
    have hD' : ∀ᵐ M ∂μ.map (rootMatrixConjugation i j 1),
        M = Matrix.diagonal (fun k => M k k) := by rwa [hroot]
    exact ae_of_ae_map (continuous_rootMatrixConjugation i j 1).measurable.aemeasurable hD'
  filter_upwards [hD, hDT] with M hM hTM
  have hz1 : M i j = 0 := by
    calc
      M i j = Matrix.diagonal (fun k => M k k) i j := congrArg (fun A => A i j) hM
      _ = 0 := Matrix.diagonal_apply_ne _ hij
  have hz2 : M j i = 0 := by
    calc
      M j i = Matrix.diagonal (fun k => M k k) j i := congrArg (fun A => A j i) hM
      _ = 0 := Matrix.diagonal_apply_ne _ (Ne.symm hij)
  have he : rootMatrixConjugation i j 1 M i j = 0 := by
    calc
      _ = Matrix.diagonal (fun k => rootMatrixConjugation i j 1 M k k) i j :=
        congrArg (fun A => A i j) hTM
      _ = 0 := Matrix.diagonal_apply_ne _ hij
  simp only [rootMatrixConjugation, Matrix.mul_transvection_apply_same,
    Matrix.transvection_mul_apply_same, hz1, hz2, one_mul, zero_add, add_zero,
    neg_mul] at he
  linarith

/-- Finite matrix measures invariant under split diagonals and the
within-block root groups are concentrated on the block-scalar algebra. -/
theorem ae_blockScalar_of_conjugation_invariance {n : ℕ}
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, μ.map (diagonalMatrixConjugation ell t) = μ)
    (r : Setoid (Fin n))
    (hroot : ∀ i j, i ≠ j → r i j → μ.map (rootMatrixConjugation i j 1) = μ) :
    ∀ᵐ M ∂μ, M ∈ blockScalarAlgebra r := by
  have hD := ae_diagonal_of_split_invariance μ ell hell hdiag
  have hE : ∀ᵐ M ∂μ, ∀ i j, r i j → M i i = M j j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · subst j
      exact Filter.Eventually.of_forall (by intros; rfl)
    · by_cases hr : r i j
      · exact (ae_diagonal_entries_eq_of_root_invariance μ hD i j hij
          (hroot i j hij hr)).mono (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (hr h).elim)
  filter_upwards [hD, hE] with M hM hE
  exact (mem_blockScalarAlgebra_iff r M).mpr ⟨hM, hE⟩

/-- The same conclusion holds at every point of the measure's support.
This is the form used by a continuous conjugation-orbit map. -/
theorem support_subset_blockScalar_of_conjugation_invariance {n : ℕ}
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, μ.map (diagonalMatrixConjugation ell t) = μ)
    (r : Setoid (Fin n))
    (hroot : ∀ i j, i ≠ j → r i j → μ.map (rootMatrixConjugation i j 1) = μ) :
    μ.support ⊆ (blockScalarAlgebra r : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  apply Measure.support_subset_of_isClosed
    (blockScalarAlgebra r).toSubmodule.closed_of_finiteDimensional
  exact ae_blockScalar_of_conjugation_invariance μ ell hell hdiag r hroot

end DukePrimeDegree

end

end OAI
