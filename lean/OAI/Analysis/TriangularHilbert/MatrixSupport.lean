import OAI.Analysis.TriangularHilbert.SignedWindowScalar

namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

theorem cyclic_sum_insert {ι : Type uι} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (f : ι → ι → ι → ℂ)
    (hf : ∀ i j k, f i j k = f j k i) :
    (∑ i ∈ insert a s, ∑ j ∈ insert a s, ∑ k ∈ insert a s, f i j k) =
      f a a a + 3 * (∑ j ∈ s, f a a j) +
        3 * (∑ j ∈ s, ∑ k ∈ s, f a j k) +
        (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k) := by
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  have h1 : (∑ i ∈ s, f a i a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hf a i a).trans (hf i a a)
  have h2 : (∑ i ∈ s, f i a a) = ∑ i ∈ s, f a a i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hf i a a
  have h3 : (∑ i ∈ s, ∑ j ∈ s, f i a j) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    simp_rw [hf _ a _]
    exact Finset.sum_comm
  have h4 : (∑ i ∈ s, ∑ j ∈ s, f i j a) = ∑ i ∈ s, ∑ j ∈ s, f a i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hf i j a).trans (hf j a i)
  rw [h1, h2, h3, h4]
  ring

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

theorem norm_quad_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖∑ j, ∑ k, star (x j) * D j k * x k‖ ≤
      ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hform : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ⟪v, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v⟫_ℂ := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec,
      dotProduct, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, v]
  rw [hform]
  calc
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := by
      gcongr
      exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
    _ = ‖D‖ * ∑ j, ‖x j‖ ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq v]
      ring

theorem column_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (i : ι) :
    (∑ j, ‖D j i‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := EuclideanSpace.single i 1
  have hn : ‖v‖ = 1 := by simp [v]
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D).le_opNorm v
  rw [hn, Matrix.l2_opNorm_toEuclideanCLM, mul_one] at h
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h
  simpa [EuclideanSpace.norm_sq_eq, v, Matrix.mulVec, dotProduct] using hs

theorem row_sq_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i : ι) :
    (∑ j, ‖D i j‖ ^ 2) ≤ ‖D‖ ^ 2 := by
  convert column_sq_sum_le D i using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← hD.apply i j, norm_star]

theorem hermitian_entry_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (i j : ι) :
    ‖D i j‖ ≤ ‖D‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖D i k‖)
    (Finset.mem_univ j)).trans (row_sq_sum_le D hD i)

theorem norm_cyclic_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i‖ ≤
      ‖D‖ * ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
  let x : ι → ℂ := fun j => if j ∈ s then (m j : ℂ) * D j i else 0
  have hf' (j k : ι) : star (x j) * D j k * x k =
      if j ∈ s then if k ∈ s then
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i else 0 else 0 := by
    by_cases hj : j ∈ s <;> by_cases hk : k ∈ s
    all_goals simp [x, hj, hk, hD.apply, mul_comm, mul_left_comm]
  have hf : (∑ j, ∑ k, star (x j) * D j k * x k) =
      ∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i := by
    simp_rw [hf']
    simp [Finset.sum_ite_mem]
  have hn' (j : ι) : ‖x j‖ ^ 2 =
      if j ∈ s then (m j) ^ 2 * ‖D i j‖ ^ 2 else 0 := by
    by_cases hj : j ∈ s
    · simp [x, hj, mul_pow, ← hD.apply i j]
    · simp [x, hj]
  have hn : (∑ j, ‖x j‖ ^ 2) = ∑ j ∈ s, (m j) ^ 2 * ‖D i j‖ ^ 2 := by
    simp_rw [hn']
    simp [Finset.sum_ite_mem]
  simpa only [hf, hn] using norm_quad_sum_le D x

theorem norm_weighted_row_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ ≤
      Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
  have hs : (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg s.subset_univ
      (fun j _ _ => sq_nonneg ‖D i j‖)).trans (row_sq_sum_le D hD i)
  have hr : Real.sqrt (∑ j ∈ s, ‖D i j‖^2) ≤ ‖D‖ :=
    (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hs⟩
  calc
    _ ≤ ∑ j ∈ s, ‖(m j : ℂ) * D i j * D j i‖ := norm_sum_le _ _
    _ = ∑ j ∈ s, (|m j| * ‖D i j‖) * ‖D i j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [← hD.apply i j]
    _ ≤ Real.sqrt (∑ j ∈ s, (|m j| * ‖D i j‖)^2) *
        Real.sqrt (∑ j ∈ s, ‖D i j‖^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ j ∈ s, (m j)^2 * ‖D i j‖^2) * ‖D‖ := by
      simp only [mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)

theorem norm_twice_tail_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (i : ι) (s : Finset ι) :
    ‖(m i : ℂ)^2 * D i i * (∑ j ∈ s, (m j : ℂ) * D i j * D j i)‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  let B := ∑ j ∈ s, (m j)^2 * ‖D i j‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYoung : |m i|^2 * ‖D i i‖ * Real.sqrt B ≤
      (|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2 := by
    have hsq := mul_nonneg (abs_nonneg (m i))
      (sq_nonneg (|m i| * ‖D i i‖ - Real.sqrt B))
    have hr := congrArg (fun z : ℝ => |m i| * z) (Real.sq_sqrt hB)
    nlinarith
  calc
    _ = |m i|^2 * ‖D i i‖ * ‖∑ j ∈ s, (m j : ℂ) * D i j * D j i‖ := by
      simp [norm_pow]
    _ ≤ |m i|^2 * ‖D i i‖ * (Real.sqrt B * ‖D‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_row_le D hD m i s) (by positivity)
    _ = ‖D‖ * (|m i|^2 * ‖D i i‖ * Real.sqrt B) := by ring
    _ ≤ ‖D‖ * ((|m i|^3 * ‖D i i‖^2 + |m i| * B) / 2) :=
      mul_le_mul_of_nonneg_left hYoung (norm_nonneg _)
    _ = _ := by dsimp [B]; ring

def spectralWeight {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j : ι) : ℝ :=
  |m i|^2 * |m j|^2 / (|m i| + |m j|) * ‖D i j‖^2

theorem spectralWeight_symm {ι : Type uι} (D : Matrix ι ι ℂ)
    (hD : D.IsHermitian) (m : ι → ℝ) (i j : ι) :
    spectralWeight D m i j = spectralWeight D m j i := by
  unfold spectralWeight
  rw [← hD.apply i j, norm_star]
  ring

theorem spectralWeight_diag {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i : ι) :
    spectralWeight D m i i = |m i|^3 * ‖D i i‖^2 / 2 := by
  unfold spectralWeight
  by_cases h : m i = 0
  · simp [h]
  · have h' : |m i| ≠ 0 := abs_ne_zero.mpr h
    field_simp
    ring

theorem spectralWeight_pair_ge {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ)
    (i j : ι) (hij : |m j| ≤ |m i|) :
    |m i| * (m j)^2 * ‖D i j‖^2 ≤ 2 * spectralWeight D m i j := by
  unfold spectralWeight
  by_cases hi : m i = 0
  · simp [hi]
  · have hp : 0 < |m i| + |m j| := add_pos_of_pos_of_nonneg (abs_pos.mpr hi) (abs_nonneg _)
    have hbase : |m i| * |m j|^2 ≤ 2 * (|m i|^2 * |m j|^2 / (|m i| + |m j|)) := by
      rw [← mul_div_assoc, le_div_iff₀ hp]
      have hmul := mul_nonneg (mul_nonneg (abs_nonneg (m i)) (sq_nonneg |m j|))
        (sub_nonneg.mpr hij)
      nlinarith
    simpa only [sq_abs, mul_assoc] using mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖D i j‖)

def cubicTerm {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) : ℂ :=
  (m i : ℂ) * (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i

theorem cubicTerm_cyclic {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) :
    cubicTerm D m i j k = cubicTerm D m j k i := by unfold cubicTerm; ring

theorem norm_cubicTerm_diag_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) :
    ‖cubicTerm D m i i i‖ ≤ ‖D‖ * (|m i|^3 * ‖D i i‖^2) := by
  calc
    _ = (|m i|^3 * ‖D i i‖^2) * ‖D i i‖ := by
      simp only [cubicTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ (|m i|^3 * ‖D i i‖^2) * ‖D‖ := by
      gcongr
      exact hermitian_entry_le D hD i i
    _ = _ := by ring

theorem norm_cubicTerm_twice_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, cubicTerm D m i i j‖ ≤
      ‖D‖ / 2 * (|m i|^3 * ‖D i i‖^2 +
        |m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  convert norm_twice_tail_le D hD m i s using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold cubicTerm
  ring

theorem norm_cubicTerm_once_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (i : ι) (s : Finset ι) :
    ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      ‖D‖ * (|m i| * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) := by
  have heq : (∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k) =
      (m i : ℂ) * (∑ j ∈ s, ∑ k ∈ s,
        (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    unfold cubicTerm
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |m i| * (‖D‖ * ∑ j ∈ s, (m j)^2 * ‖D i j‖^2) :=
      mul_le_mul_of_nonneg_left (norm_cyclic_tail_le D hD m i s) (abs_nonneg _)
    _ = _ := by ring

theorem spectralWeight_insert_ge {ι : Type uι} [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ)
    (s : Finset ι) (a : ι) (ha : a ∉ s) (hmax : ∀ j ∈ s, |m j| ≤ |m a|) :
    |m a|^3 * ‖D a a‖^2 / 2 +
      |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 +
      (∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j) ≤
      ∑ i ∈ insert a s, ∑ j ∈ insert a s, spectralWeight D m i j := by
  have hrs : (∑ j ∈ s, spectralWeight D m j a) =
      ∑ j ∈ s, spectralWeight D m a j := by
    apply Finset.sum_congr rfl
    intro j _
    exact spectralWeight_symm D hD m j a
  have hp : |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2 ≤
      2 * ∑ j ∈ s, spectralWeight D m a j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_assoc] using spectralWeight_pair_ge D m a j (hmax j hj)
  simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
  rw [hrs, spectralWeight_diag]
  linarith

theorem norm_cubic_sum_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) (s : Finset ι) :
    ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ ≤
      5 * ‖D‖ * ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j := by
  induction s using Finset.induction_on_max_value (fun i => |m i|) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [cyclic_sum_insert s a ha _ (cubicTerm_cyclic D m)]
    let A := |m a|^3 * ‖D a a‖^2
    let E := |m a| * ∑ j ∈ s, (m j)^2 * ‖D a j‖^2
    let Q := ∑ i ∈ s, ∑ j ∈ s, spectralWeight D m i j
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hdiag := norm_cubicTerm_diag_le D hD m a
    have htwice := norm_cubicTerm_twice_le D hD m a s
    have honce := norm_cubicTerm_once_le D hD m a s
    calc
      _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j +
          3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := norm_add_le _ _
      _ ≤ (‖cubicTerm D m a a a‖ + 3 * ‖∑ j ∈ s, cubicTerm D m a a j‖ +
          3 * ‖∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖) +
          ‖∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m i j k‖ := by
        gcongr
        calc
          _ ≤ ‖cubicTerm D m a a a + 3 * ∑ j ∈ s, cubicTerm D m a a j‖ +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := norm_add_le _ _
          _ ≤ (‖cubicTerm D m a a a‖ + ‖3 * ∑ j ∈ s, cubicTerm D m a a j‖) +
              ‖3 * ∑ j ∈ s, ∑ k ∈ s, cubicTerm D m a j k‖ := by
            gcongr
            exact norm_add_le _ _
          _ = _ := by simp
      _ ≤ (‖D‖ * A + 3 * (‖D‖ / 2 * (A + E)) + 3 * (‖D‖ * E)) +
          5 * ‖D‖ * Q := by
        exact add_le_add (add_le_add (add_le_add hdiag
          (mul_le_mul_of_nonneg_left htwice (by norm_num)))
          (mul_le_mul_of_nonneg_left honce (by norm_num))) ih
      _ ≤ 5 * ‖D‖ * (A / 2 + E + Q) := by
        nlinarith [mul_nonneg (norm_nonneg D) hE]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (spectralWeight_insert_ge D hD m s a ha hmax) (by positivity)

theorem trace_cube_mul_diagonal {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (m : ι → ℝ) :
    Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      ∑ i, ∑ j, ∑ k, cubicTerm D m i j k := by
  have expand (A : Matrix ι ι ℂ) :
      Matrix.trace (A^3) = ∑ i, ∑ j, ∑ k, A i j * (A j k * A k i) := by
    have hp : A^3 = A * (A * A) := by noncomm_ring
    rw [hp]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  rw [expand]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold cubicTerm
  ring

theorem norm_trace_cube_mul_diagonal_le {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (m : ι → ℝ) :
    ‖Matrix.trace ((D * Matrix.diagonal (fun i => (m i : ℂ)))^3)‖ ≤
      5 * ‖D‖ * ∑ i, ∑ j, spectralWeight D m i j := by
  rw [trace_cube_mul_diagonal]
  exact norm_cubic_sum_le D hD m Finset.univ

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

def traceReal (A : Matrix ι ι ℂ) : ℝ := A.trace.re

@[simp] theorem traceReal_add (A B : Matrix ι ι ℂ) :
    traceReal (A + B) = traceReal A + traceReal B := by simp [traceReal]
@[simp] theorem traceReal_sub (A B : Matrix ι ι ℂ) :
    traceReal (A - B) = traceReal A - traceReal B := by simp [traceReal]
@[simp] theorem traceReal_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    traceReal (c • A) = c * traceReal A := by simp [traceReal]
@[simp] theorem traceReal_zero : traceReal (0 : Matrix ι ι ℂ) = 0 := by simp [traceReal]
@[simp] theorem traceReal_star (A : Matrix ι ι ℂ) : traceReal Aᴴ = traceReal A := by
  simp [traceReal]
theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem traceReal_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ traceReal A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

def hsReal (X Y : Matrix ι ι ℂ) : ℝ := traceReal (Xᴴ * Y)

@[simp] theorem hsReal_add_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X + Y) Z = hsReal X Z + hsReal Y Z := by
  simp [hsReal, add_mul]
@[simp] theorem hsReal_add_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y + Z) = hsReal X Y + hsReal X Z := by
  simp [hsReal, mul_add]
@[simp] theorem hsReal_sub_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X - Y) Z = hsReal X Z - hsReal Y Z := by
  simp [hsReal, sub_mul]
@[simp] theorem hsReal_sub_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y - Z) = hsReal X Y - hsReal X Z := by
  simp [hsReal, mul_sub]
@[simp] theorem hsReal_smul_left (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal (c • X) Y = c * hsReal X Y := by
  simp [hsReal, Matrix.smul_mul]
@[simp] theorem hsReal_smul_right (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal X (c • Y) = c * hsReal X Y := by
  simp [hsReal, Matrix.mul_smul]
@[simp] theorem hsReal_zero_right (X : Matrix ι ι ℂ) : hsReal X 0 = 0 := by simp [hsReal]

theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

def sylv (A X : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * X + X * A

@[simp] theorem sylv_add_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X + Y) = sylv A X + sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_sub_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X - Y) = sylv A X - sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_smul_right (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv A (c • X) = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_smul_left (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv (c • A) X = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_sub_left (A B X : Matrix ι ι ℂ) :
    sylv (A - B) X = sylv A X - sylv B X := by unfold sylv; noncomm_ring
@[simp] theorem sylv_zero_right (A : Matrix ι ι ℂ) : sylv A 0 = 0 := by simp [sylv]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

def penalty (A X : Matrix ι ι ℂ) : ℝ := hsReal X (sylv A X)

theorem penalty_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (X : Matrix ι ι ℂ) : 0 ≤ penalty A X := by
  simp only [penalty, hsReal, sylv, mul_add, traceReal_add]
  have h₁ := traceReal_nonneg (hA.conjTranspose_mul_mul_same X)
  have h₂ := traceReal_nonneg (hA.mul_mul_conjTranspose_same X)
  rw [Matrix.mul_assoc] at h₁
  rw [← Matrix.mul_assoc Xᴴ X A, traceReal_mul_cycle Xᴴ X A,
    traceReal_mul_cycle A Xᴴ X]
  exact add_nonneg h₁ h₂

theorem penalty_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    penalty A (X - Y) = penalty A X + penalty A Y - 2 * hsReal (sylv A Y) X := by
  simp only [penalty, sylv_sub_right, hsReal_sub_left, hsReal_sub_right]
  rw [hsReal_symm Y (sylv A X), ← hsReal_sylv_symm hA, hsReal_symm X (sylv A Y)]
  ring

theorem penalty_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (X : Matrix ι ι ℂ) :
    penalty A X ≤ penalty B X := by
  have h := penalty_nonneg hAB X
  simpa only [penalty, sylv_sub_left, hsReal_sub_right, sub_nonneg] using h

def variation (A K X : Matrix ι ι ℂ) : ℝ := 2 * hsReal K X - penalty A X

def rootCost (A K : Matrix ι ι ℂ) : ℝ := (3 / 2 : ℝ) * sSup (Set.range (variation A K))

theorem variation_sylv {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    variation A (sylv A Y) X = penalty A Y - penalty A (X - Y) := by
  rw [variation, penalty_sub hA]
  ring

theorem rootCost_eq_of_solution {A K Y : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hY : sylv A Y = K) : rootCost A K = (3 / 2 : ℝ) * hsReal K Y := by
  subst K
  have heq : sSup (Set.range (variation A (sylv A Y))) = penalty A Y := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)
    · rintro _ ⟨X, rfl⟩
      rw [variation_sylv hA.isHermitian]
      exact sub_le_self _ (penalty_nonneg hA (X - Y))
    · intro w hw
      refine ⟨variation A (sylv A Y) Y, ⟨Y, rfl⟩, ?_⟩
      simpa [variation_sylv hA.isHermitian, penalty] using hw
  rw [rootCost, heq]
  congr 1
  exact hsReal_symm _ _

theorem variation_bddAbove {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : BddAbove (Set.range (variation A K)) := by
  obtain ⟨Y, rfl⟩ := hsol
  refine ⟨penalty A Y, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [variation_sylv hA.isHermitian]
  exact sub_le_self _ (penalty_nonneg hA _)

theorem variation_le_rootCost {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (X : Matrix ι ι ℂ) :
    (3 / 2 : ℝ) * variation A K X ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩

theorem rootCost_nonneg {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : 0 ≤ rootCost A K := by
  simpa [variation, penalty] using variation_le_rootCost hA hsol 0

theorem rootCost_antitone {A B K : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    rootCost B K ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans
    (le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩)

theorem rootCost_scale {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) {c : ℝ} (hc : 0 < c) :
    rootCost (c • A) K = c⁻¹ * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hY' : sylv (c • A) (c⁻¹ • Y) = K := by
    simp [sylv_smul_left, sylv_smul_right, smul_smul, ne_of_gt hc, hY]
  rw [rootCost_eq_of_solution (hA.smul (le_of_lt hc)) hY',
    rootCost_eq_of_solution hA hY, hsReal_smul_right]
  ring

theorem hsReal_eq_sum (X Y : Matrix ι ι ℂ) :
    hsReal X Y = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  simp only [hsReal, traceReal, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

variable [DecidableEq ι]

theorem sylv_diagonal_apply (q : ι → ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) X i j =
      ((q i + q j : ℝ) : ℂ) * X i j := by
  simp only [sylv, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Complex.ofReal_add]
  ring

def diagonalSolution (q : ι → ℝ) (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => K i j / ((q i + q j : ℝ) : ℂ)

theorem diagonalSolution_solves (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (diagonalSolution q K) = K := by
  ext i j
  rw [sylv_diagonal_apply]
  by_cases h : q i + q j = 0
  · simp [diagonalSolution, h, hsupp i j h]
  · exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr h)

theorem rootCost_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (K : Matrix ι ι ℂ) (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    rootCost (Matrix.diagonal (fun i => (q i : ℂ))) K =
      (3 / 2 : ℝ) * ∑ i, ∑ j, ‖K i j‖^2 / (q i + q j) := by
  have hq' : (Matrix.diagonal (fun i => (q i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hq i))
  rw [rootCost_eq_of_solution hq' (diagonalSolution_solves q K hsupp), hsReal_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [diagonalSolution, ← mul_div_assoc, RCLike.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_re, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem hsReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X Y : Matrix ι ι ℂ) :
    hsReal (conjStarAlgAut ℂ _ U X) (conjStarAlgAut ℂ _ U Y) = hsReal X Y := by
  change traceReal (star (conjStarAlgAut ℂ _ U X) * conjStarAlgAut ℂ _ U Y) = _
  rw [← map_star, ← map_mul, traceReal_unitary_conj]
  rfl

theorem sylv_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A X : Matrix ι ι ℂ) :
    sylv (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U X) =
      conjStarAlgAut ℂ _ U (sylv A X) := by simp only [sylv, map_add, map_mul]

theorem variation_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K X : Matrix ι ι ℂ) :
    variation (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K)
      (conjStarAlgAut ℂ _ U X) = variation A K X := by
  simp only [variation, penalty, sylv_unitary_conj, hsReal_unitary_conj]

theorem rootCost_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K : Matrix ι ι ℂ) :
    rootCost (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K) = rootCost A K := by
  unfold rootCost
  congr 2
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := (conjStarAlgAut ℂ _ U).surjective X
    exact ⟨Y, (variation_unitary_conj U A K Y).symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨conjStarAlgAut ℂ _ U X, variation_unitary_conj U A K X⟩

def hessianCost (P K : Matrix ι ι ℂ) : ℝ := rootCost (CFC.sqrt P) K

theorem exists_sylv_solution {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsupp : ∀ i j, hA.eigenvalues i + hA.eigenvalues j = 0 →
      conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) K i j = 0) :
    ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let K' := conjStarAlgAut ℂ _ (star U) K
  let Y := diagonalSolution hA.eigenvalues K'
  refine ⟨conjStarAlgAut ℂ _ U Y, ?_⟩
  have hy : sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y = K' :=
    diagonalSolution_solves _ _ hsupp
  have hh := congrArg (conjStarAlgAut ℂ _ U) hy
  rw [← sylv_unitary_conj] at hh
  have ha : conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) = A :=
    hA.spectral_theorem.symm
  rw [ha] at hh
  simpa only [K', ← conjStarAlgAut_mul_apply, Unitary.mul_star_self, map_one,
    StarAlgEquiv.one_apply] using hh

theorem exists_sylv_solution_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (K : Matrix ι ι ℂ) : ∃ Y, sylv A Y = K := by
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  exact False.elim ((ne_of_gt (add_pos (hA.eigenvalues_pos i)
    (hA.eigenvalues_pos j))) hij)

theorem hessianCost_antitone {P Q K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (hPQ : P ≤ Q) :
    hessianCost Q K ≤ hessianCost P K := by
  exact rootCost_antitone (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol (CFC.monotone_sqrt hPQ)

def sylvLinear (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := sylv A
  map_add' := sylv_add_right A
  map_smul' c X := sylv_smul_right c A X

def sylvEquiv {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (LinearEquiv.ofBijective (sylvLinear A)
    (let hs : Function.Surjective (sylvLinear A) := exists_sylv_solution_posDef hA
     ⟨(LinearMap.injective_iff_surjective).mpr hs, hs⟩)).toContinuousLinearEquiv

theorem hasFDerivAt_square {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => X * X) (sylvEquiv hA : _ →L[ℝ] _) A := by
  convert! (hasFDerivAt_id A (𝕜 := ℝ)).mul' (hasFDerivAt_id A (𝕜 := ℝ)) using 1

theorem contDiff_square {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun X : Matrix ι ι ℂ => X * X) := contDiff_id.mul contDiff_id

theorem sqrt_smul {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • P) = Real.sqrt c • CFC.sqrt P := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg P)

theorem sqrt_smoothWithin_posDef {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ContDiffWithinAt ℝ ∞ CFC.sqrt {Q : Matrix ι ι ℂ | 0 ≤ Q} P ∧
    HasFDerivWithinAt CFC.sqrt
      ((sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm : _ →L[ℝ] _)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let f : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X => X * X
  have hc : ContDiffAt ℝ ∞ f A := contDiff_square.contDiffAt
  have hd : HasFDerivAt f (sylvEquiv hA : _ →L[ℝ] _) A := hasFDerivAt_square hA
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let g := hc.localInverse hd hn
  have hstrict := hc.hasStrictFDerivAt' hd hn
  have hAP : f A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hgC : ContDiffAt ℝ ∞ g P := hAP ▸ hc.to_localInverse hd hn
  have hgD : HasFDerivAt g ((sylvEquiv hA).symm : _ →L[ℝ] _) P :=
    hAP ▸ hstrict.to_localInverse.hasFDerivAt
  have heq : g =ᶠ[nhdsWithin P {Q : Matrix ι ι ℂ | 0 ≤ Q}] CFC.sqrt := by
    have ht := (CFC.continuousOn_sqrt P hP.posSemidef.nonneg).eventually
      hstrict.eventually_left_inverse
    filter_upwards [ht, self_mem_nhdsWithin] with Q hQ hQpos
    change g (CFC.sqrt Q * CFC.sqrt Q) = CFC.sqrt Q at hQ
    rwa [CFC.sqrt_mul_sqrt_self Q hQpos] at hQ
  refine ⟨hgC.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq.symm
    hP.posSemidef.nonneg, ?_⟩
  exact hgD.hasFDerivWithinAt.congr_of_eventuallyEq heq.symm
    (heq.symm.self_of_nhdsWithin hP.posSemidef.nonneg)

def traceRealCLM : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (show Matrix ι ι ℂ →ₗ[ℝ] ℝ from
    { toFun := traceReal
      map_add' := traceReal_add
      map_smul' := traceReal_smul }).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem traceRealCLM_apply (X : Matrix ι ι ℂ) :
    traceRealCLM X = traceReal X := rfl

def energy (P : Matrix ι ι ℂ) : ℝ := traceReal (P * CFC.sqrt P)

def energyGradient (P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 / 2 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) (CFC.sqrt P))

@[simp] theorem energyGradient_apply (P K : Matrix ι ι ℂ) :
    energyGradient P K = (3 / 2 : ℝ) * traceReal (CFC.sqrt P * K) := rfl

theorem traceReal_mul_sylv (A Y : Matrix ι ι ℂ) :
    traceReal (A * sylv A Y) = 2 * traceReal (A * A * Y) := by
  simp only [sylv, mul_add, traceReal_add]
  simp only [← Matrix.mul_assoc]
  rw [traceReal_mul_cycle A Y A]
  ring

theorem energy_hasFDerivWithinAt {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    HasFDerivWithinAt energy (energyGradient P)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let e := sylvEquiv hA
  have hd := (sqrt_smoothWithin_posDef hP).2
  change HasFDerivWithinAt CFC.sqrt (e.symm : _ →L[ℝ] _) _ P at hd
  have hmul := (hasFDerivWithinAt_id (s := {Q : Matrix ι ι ℂ | 0 ≤ Q})
    P (𝕜 := ℝ)).mul' hd
  have h := traceRealCLM.hasFDerivAt.comp_hasFDerivWithinAt P hmul
  apply h.congr_fderiv
  ext K
  change traceReal (P * e.symm K + K * A) =
    (3 / 2 : ℝ) * traceReal (A * K)
  have he : sylv A (e.symm K) = K := e.apply_symm_apply K
  have hp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have ht := traceReal_mul_sylv A (e.symm K)
  rw [he, hp] at ht
  rw [traceReal_add, traceReal_mul_comm K A]
  linarith

theorem hsReal_single (K : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    hsReal K (Matrix.single i j z) = (star (K i j) * z).re := by
  simp [hsReal_eq_sum, Matrix.single_apply, ite_and, apply_ite]

theorem sylv_diagonal_single (q : ι → ℝ) (i j : ι) (z : ℂ) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (Matrix.single i j z) =
      Matrix.single i j (((q i + q j : ℝ) : ℂ) * z) := by
  ext a b
  rw [sylv_diagonal_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b; simp
    · simp [hb]
  · simp [ha]

theorem sylv_solvable_diagonal_of_bddAbove (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hb : BddAbove (Set.range (variation (Matrix.diagonal (fun i => (q i : ℂ))) K))) :
    ∃ Y, sylv (Matrix.diagonal (fun i => (q i : ℂ))) Y = K := by
  refine ⟨diagonalSolution q K, diagonalSolution_solves q K ?_⟩
  intro i j hij
  by_contra hK
  obtain ⟨b, hb⟩ := hb
  let X := Matrix.single i j (K i j)
  have hzero : sylv (Matrix.diagonal (fun i => (q i : ℂ))) X = 0 := by
    simp [X, sylv_diagonal_single, hij]
  have hhs : hsReal K X = ‖K i j‖^2 := by
    rw [hsReal_single]
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖K i j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hK)
  let t : ℝ := b / (2 * ‖K i j‖^2) + 1
  have ht := hb (Set.mem_range_self (t • X))
  change variation _ K (t • X) ≤ b at ht
  simp only [variation, penalty, sylv_smul_right, hzero, smul_zero,
    hsReal_zero_right, sub_zero, hsReal_smul_right, hhs] at ht
  have hcalc : 2 * (t * ‖K i j‖^2) = b + 2 * ‖K i j‖^2 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  rw [hcalc] at ht
  linarith

theorem sylv_solvable_of_bddAbove {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hb : BddAbove (Set.range (variation A K))) : ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let K' := f K
  have hAd : f A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb' : BddAbove (Set.range (variation (f A) K')) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b, ?_⟩
    rintro _ ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := f.surjective X
    change variation (f A) (f K) (f Y) ≤ b
    exact (variation_unitary_conj (star U) A K Y) ▸ hb (Set.mem_range_self Y)
  rw [hAd] at hb'
  obtain ⟨Y, hY⟩ := sylv_solvable_diagonal_of_bddAbove _ K' hb'
  refine ⟨f.symm Y, ?_⟩
  apply f.injective
  change f (sylv A (f.symm Y)) = f K
  calc
    _ = sylv (f A) (f (f.symm Y)) := (sylv_unitary_conj (star U) A (f.symm Y)).symm
    _ = sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y := by
      rw [f.apply_symm_apply, hAd]
    _ = _ := hY

theorem sylv_solvable_mono {A B K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    ∃ Y, sylv B Y = K := by
  apply sylv_solvable_of_bddAbove hB
  obtain ⟨b, hb⟩ := variation_bddAbove hA hsol
  refine ⟨b, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans (hb (Set.mem_range_self X))

omit [DecidableEq ι] in
theorem rootCost_smul_direction {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (c : ℝ) :
    rootCost A (c • K) = c^2 * rootCost A K := by
  obtain ⟨Y, hY⟩ := hsol
  have hc : sylv A (c • Y) = c • K := by rw [sylv_smul_right, hY]
  rw [rootCost_eq_of_solution hA hc, rootCost_eq_of_solution hA hY,
    hsReal_smul_left, hsReal_smul_right]
  ring

omit [DecidableEq ι] in
theorem penalty_three_identity (A X Y Z : Matrix ι ι ℂ) :
    3 * (penalty A X + penalty A Y + penalty A Z) - penalty A (X + Y + Z) =
      penalty A (X - Y) + penalty A (Y - Z) + penalty A (Z - X) := by
  simp only [penalty, sylv_add_right, sylv_sub_right, hsReal_add_left,
    hsReal_add_right, hsReal_sub_left, hsReal_sub_right]
  ring

omit [DecidableEq ι] in
theorem rootCost_three_le {A K L M : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : ∃ X, sylv A X = K) (hL : ∃ Y, sylv A Y = L)
    (hM : ∃ Z, sylv A Z = M) :
    rootCost A (K + L + M) ≤ 3 * (rootCost A K + rootCost A L + rootCost A M) := by
  obtain ⟨X, rfl⟩ := hK
  obtain ⟨Y, rfl⟩ := hL
  obtain ⟨Z, rfl⟩ := hM
  have hall : sylv A (X + Y + Z) = sylv A X + sylv A Y + sylv A Z := by simp
  rw [rootCost_eq_of_solution hA hall, rootCost_eq_of_solution hA rfl,
    rootCost_eq_of_solution hA rfl, rootCost_eq_of_solution hA rfl]
  rw [← hall]
  have hc := penalty_three_identity A X Y Z
  have hn := add_nonneg (add_nonneg (penalty_nonneg hA (X - Y))
    (penalty_nonneg hA (Y - Z))) (penalty_nonneg hA (Z - X))
  rw [hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _,
    hsReal_symm (sylv A _) _, hsReal_symm (sylv A _) _]
  change (3 / 2 : ℝ) * penalty A (X + Y + Z) ≤
    3 * ((3 / 2 : ℝ) * penalty A X + (3 / 2 : ℝ) * penalty A Y +
      (3 / 2 : ℝ) * penalty A Z)
  linarith

omit [Fintype ι] [DecidableEq ι] in

theorem gram_diag_eq_zero_iff {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (j : ι) :
    (Rᴴ * R) j j = 0 ↔ ∀ i, R i j = 0 := by
  change star (fun i => R i j) ⬝ᵥ (fun i => R i j) = 0 ↔ _
  rw [dotProduct_star_self_eq_zero]
  exact funext_iff

theorem sylv_solvable_inserted_gram {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (D : Matrix κ κ ℂ) :
    ∃ Y, sylv (CFC.sqrt (Rᴴ * R)) Y = Rᴴ * D * R := by
  let P := Rᴴ * R
  let A := CFC.sqrt P
  have hP : P.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  let U := hA.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let R' := R * (U : Matrix ι ι ℂ)
  let q := hA.isHermitian.eigenvalues
  have hAd : f A = Matrix.diagonal (fun i => (q i : ℂ)) :=
    hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hAp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hGram : R'ᴴ * R' = f P := by
    simp only [R', f, P, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hIns : f (Rᴴ * D * R) = R'ᴴ * D * R' := by
    simp only [R', f, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  have hj : q j = 0 :=
    ((add_eq_zero_iff_of_nonneg (hA.eigenvalues_nonneg i)
      (hA.eigenvalues_nonneg j)).mp hij).2
  have hdiag : (R'ᴴ * R') j j = 0 := by
    rw [hGram, ← hAp, map_mul, hAd, Matrix.diagonal_mul_diagonal]
    simp [hj]
  have hcol := (gram_diag_eq_zero_iff R' j).mp hdiag
  change f (Rᴴ * D * R) i j = 0
  rw [hIns]
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem trace_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    Matrix.trace (conjStarAlgAut ℂ _ U X) = Matrix.trace X := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem norm_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    ‖conjStarAlgAut ℂ _ U X‖ = ‖X‖ := by
  rw [conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem hermitian_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (conjStarAlgAut ℂ _ U X).IsHermitian := by
  change star (conjStarAlgAut ℂ _ U X) = conjStarAlgAut ℂ _ U X
  rw [← map_star]
  exact congrArg (conjStarAlgAut ℂ _ U) hX

theorem sqrt_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    CFC.sqrt (conjStarAlgAut ℂ _ U P) = conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
        (U : Matrix ι ι ℂ)).nonneg

theorem hessianCost_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (K : Matrix ι ι ℂ) :
    hessianCost (conjStarAlgAut ℂ _ U P) (conjStarAlgAut ℂ _ U K) =
      hessianCost P K := by
  simp only [hessianCost, sqrt_unitary_conj U hP, rootCost_unitary_conj]

theorem sqrt_diagonal_square (m : ι → ℝ) :
    CFC.sqrt (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ))) =
      Matrix.diagonal (fun i => ((|m i| : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    change ((|m i| : ℝ) : ℂ) * ((|m i| : ℝ) : ℂ) = (m i : ℂ) * (m i : ℂ)
    exact_mod_cast (show |m i| * |m i| = m i * m i by nlinarith [sq_abs (m i)])
  · exact (Matrix.PosSemidef.diagonal
      (fun i => RCLike.ofReal_nonneg.mpr (abs_nonneg (m i)))).nonneg

theorem hessianCost_diagonal_square (m : ι → ℝ) (D : Matrix ι ι ℂ) :
    hessianCost (Matrix.diagonal (fun i => (m i : ℂ)) *
      Matrix.diagonal (fun i => (m i : ℂ)))
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
       Matrix.diagonal (fun i => (m i : ℂ))) =
      (3 / 2 : ℝ) * ∑ i, ∑ j, spectralWeight D m i j := by
  unfold hessianCost
  rw [sqrt_diagonal_square]
  have hs : ∀ i j, |m i| + |m j| = 0 →
      (Matrix.diagonal (fun i => (m i : ℂ)) * D *
        Matrix.diagonal (fun i => (m i : ℂ))) i j = 0 := by
    intro i j hij
    have hi : m i = 0 := abs_eq_zero.mp
      ((add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).mp hij).1
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hi]
  rw [rootCost_diagonal _ (fun i => abs_nonneg (m i)) _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [spectralWeight, Matrix.mul_diagonal, Matrix.diagonal_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  ring

theorem norm_trace_cube_le_hessian (M D : Matrix ι ι ℂ)
    (hM : M.IsHermitian) (hD : D.IsHermitian) :
    ‖Matrix.trace ((D * M)^3)‖ ≤
      (10 / 3 : ℝ) * ‖D‖ * hessianCost (M * M) (M * D * M) := by
  let U := star hM.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D' := f D
  let m := hM.eigenvalues
  have hM' : f M = Matrix.diagonal (fun i => (m i : ℂ)) :=
    hM.conjStarAlgAut_star_eigenvectorUnitary
  have hd : D'.IsHermitian := hermitian_unitary_conj U hD
  have hn : ‖D'‖ = ‖D‖ := norm_unitary_conj U D
  have ht : Matrix.trace ((D' * Matrix.diagonal (fun i => (m i : ℂ)))^3) =
      Matrix.trace ((D * M)^3) := by
    rw [← hM', ← map_mul, ← map_pow]
    exact trace_unitary_conj U _
  have hp : (M * M).PosSemidef := by
    simpa only [hM.eq] using Matrix.posSemidef_conjTranspose_mul_self M
  have hc := hessianCost_unitary_conj U hp (M * D * M)
  change hessianCost (f (M * M)) (f (M * D * M)) = _ at hc
  simp only [map_mul, hM'] at hc
  rw [hessianCost_diagonal_square] at hc
  have hb := norm_trace_cube_mul_diagonal_le D' hd m
  rw [ht, hn] at hb
  rw [← hc]
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

abbrev Three := Fin 3
abbrev BlockSpace (ι : Type uι) := Three × ι
abbrev blocks (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix (BlockSpace ι) (BlockSpace ι) ℂ := Matrix.comp _ _ _ _ _ A

omit [DecidableEq ι] in
theorem blocks_mul (A B : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks (A * B) = blocks A * blocks B := by
  exact (Matrix.compRingEquiv Three ι ℂ).map_mul A B

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_star (A : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks Aᴴ = (blocks A)ᴴ := rfl

omit [DecidableEq ι] in
theorem blocks_trace (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix.trace (blocks A) = ∑ v, Matrix.trace (A v v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]

def triangleBlocks (W : Three → Matrix ι ι ℂ) : Matrix Three Three (Matrix ι ι ℂ) :=
  fun i j => if i = 0 then (if j = 0 then 0 else if j = 1 then W 0 else (W 2)ᴴ)
    else if i = 1 then (if j = 0 then (W 0)ᴴ else if j = 1 then 0 else W 1)
    else (if j = 0 then W 2 else if j = 1 then (W 1)ᴴ else 0)

def triangle (W : Three → Matrix ι ι ℂ) := blocks (triangleBlocks W)
def blockD (D : Three → Matrix ι ι ℂ) := blocks (Matrix.diagonal D)

omit [Fintype ι] [DecidableEq ι] in
theorem triangle_hermitian (W : Three → Matrix ι ι ℂ) :
    (triangle W).IsHermitian := by
  change (blocks (triangleBlocks W))ᴴ = blocks (triangleBlocks W)
  rw [← blocks_star]
  congr 1
  ext v w i j
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks, Matrix.conjTranspose_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem blockD_hermitian (D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) : (blockD D).IsHermitian := by
  unfold blockD
  change (blocks (Matrix.diagonal D))ᴴ = blocks (Matrix.diagonal D)
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  have hs : star D = D := funext hD
  rw [hs]

theorem triangle_trace_cube (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    Matrix.trace ((blockD D * triangle W)^3) =
      (6 : ℂ) * (Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  have hreverse :
      Matrix.trace (D 0 * (W 2)ᴴ * D 2 * (W 1)ᴴ * D 1 * (W 0)ᴴ) = star τ := by
    simp only [τ, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (hD _).eq,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hrot (A B C E F G : Matrix ι ι ℂ) :
      Matrix.trace (A * B * C * E * F * G) =
        Matrix.trace (F * G * A * B * C * E) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A * B) (C * E) (F * G)
  have hf1 := hrot (D 1) (W 1) (D 2) (W 2) (D 0) (W 0)
  have hf2 := (hrot (D 2) (W 2) (D 0) (W 0) (D 1) (W 1)).trans hf1
  have hr2 := hrot (D 2) (W 1)ᴴ (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ
  have hr1 := (hrot (D 1) (W 0)ᴴ (D 0) (W 2)ᴴ (D 2) (W 1)ᴴ).trans hr2
  simp only [Matrix.mul_assoc] at hf1 hf2 hr1 hr2 hreverse
  unfold blockD triangle
  rw [← blocks_mul, pow_three, ← blocks_mul, ← blocks_mul, blocks_trace]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, triangleBlocks,
    zero_mul, mul_zero, add_zero, zero_add, ite_true, ite_false, Fin.reduceEq,
    mul_add, add_mul, Matrix.trace_add, Matrix.mul_assoc]
  simp only [Matrix.trace_zero, add_zero, zero_add]
  rw [hf1, hf2, hr1, hr2, hreverse]
  simp only [← Matrix.mul_assoc]
  change τ + star τ + (star τ + τ) + (τ + star τ) = (6 : ℂ) * (τ.re : ℂ)
  apply Complex.ext <;> simp [RCLike.star_def, Complex.mul_re, Complex.mul_im]
  ring

def vertexProj (v : Three) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => if a.1 = v then 1 else 0)

omit [Fintype ι] in
theorem vertexProj_hermitian (v : Three) : (vertexProj (ι := ι) v).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change star (if i.1 = v then (1 : ℂ) else 0) = _
  split_ifs <;> simp

theorem vertexProj_sq (v : Three) : vertexProj (ι := ι) v * vertexProj v = vertexProj v := by
  simp only [vertexProj, Matrix.diagonal_mul_diagonal]
  congr 1
  ext a
  split_ifs <;> simp

omit [Fintype ι] in
theorem sum_vertexProj : ∑ v, vertexProj (ι := ι) v = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [vertexProj, Matrix.sum_apply]
  · simp [vertexProj, Matrix.sum_apply, hab]

theorem vertexProj_commute_blockD (v : Three) (D : Three → Matrix ι ι ℂ) :
    vertexProj v * blockD D = blockD D * vertexProj v := by
  ext a b
  simp only [vertexProj, Matrix.diagonal_mul, Matrix.mul_diagonal, blockD,
    Matrix.comp_apply, Matrix.diagonal_apply]
  by_cases hab : a.1 = b.1
  · simp [hab]
  · simp [hab]

def rowStar (W : Three → Matrix ι ι ℂ) (v : Three) := vertexProj v * triangle W

def starGram (W : Three → Matrix ι ι ℂ) (v : Three) := (rowStar W v)ᴴ * rowStar W v

def starInsert (W D : Three → Matrix ι ι ℂ) (v : Three) :=
  (rowStar W v)ᴴ * blockD D * rowStar W v

theorem starGram_eq (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = triangle W * vertexProj v * triangle W := by
  simp only [starGram, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (triangle W), vertexProj_sq]

theorem starInsert_eq (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = triangle W * vertexProj v * blockD D * triangle W := by
  simp only [starInsert, rowStar, Matrix.conjTranspose_mul,
    (vertexProj_hermitian v).eq, (triangle_hermitian W).eq]
  have hp := vertexProj_commute_blockD v D
  calc
    _ = triangle W * (vertexProj v * (blockD D * vertexProj v)) * triangle W := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hp, ← Matrix.mul_assoc (vertexProj v), vertexProj_sq];
                simp only [Matrix.mul_assoc]

theorem sum_starGram (W : Three → Matrix ι ι ℂ) :
    ∑ v, starGram W v = triangle W * triangle W := by
  simp_rw [starGram_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem sum_starInsert (W D : Three → Matrix ι ι ℂ) :
    ∑ v, starInsert W D v = triangle W * blockD D * triangle W := by
  simp_rw [starInsert_eq]
  rw [← Matrix.sum_mul, ← Matrix.sum_mul, ← Matrix.mul_sum, sum_vertexProj, mul_one]

theorem starGram_le (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v ≤ triangle W * triangle W := by
  rw [← sum_starGram]
  exact Finset.single_le_sum (fun w _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar W w)).nonneg) (Finset.mem_univ v)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_common_three (P K : Fin 3 → Matrix ι ι ℂ)
    {Q : Matrix ι ι ℂ} (hPQ : ∀ v, P v ≤ Q)
    (hsol : ∀ v, ∃ X, sylv (CFC.sqrt (P v)) X = K v) :
    hessianCost Q (∑ v, K v) ≤ 3 * ∑ v, hessianCost (P v) (K v) := by
  have hq : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hsolQ (v : Fin 3) : ∃ X, sylv (CFC.sqrt Q) X = K v :=
    sylv_solvable_mono (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v)))
      hq.isHermitian (hsol v) (CFC.monotone_sqrt (hPQ v))
  calc
    _ ≤ 3 * ∑ v, hessianCost Q (K v) := by
      simpa only [Fin.sum_univ_three, hessianCost] using
        rootCost_three_le hq (hsolQ 0) (hsolQ 1) (hsolQ 2)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
      (fun v _ => hessianCost_antitone (hsol v) (hPQ v))) (by norm_num)

theorem triangle_common_metric (W D : Three → Matrix ι ι ℂ) :
    hessianCost (triangle W * triangle W) (triangle W * blockD D * triangle W) ≤
      3 * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  rw [← sum_starInsert]
  exact hessianCost_common_three (starGram W) (starInsert W D)
    (starGram_le W) (fun v => sylv_solvable_inserted_gram (rowStar W v) (blockD D))

theorem triangle_real_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    |(Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)).re| ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  have h := norm_trace_cube_le_hessian (triangle W) (blockD D)
    (triangle_hermitian W) (blockD_hermitian D hD)
  rw [triangle_trace_cube W D hD, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hm := triangle_common_metric W D
  have hc := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (10 / 3 : ℝ) * ‖blockD D‖ by positivity)
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def diagonalUnitary (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) : unitary (Matrix ι ι ℂ) :=
  ⟨Matrix.diagonal c, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    have hci (i : ι) : star (c i) * c i = 1 := by
      simpa only [RCLike.star_def, mul_comm, hc, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (c i)
    ext i j
    by_cases hij : i = j
    · subst j; simpa using hci i
    · simp [hij]⟩

theorem insertedCost_right_unitary (R L : Matrix ι ι ℂ)
    (U : unitary (Matrix ι ι ℂ)) :
    hessianCost ((R * (U : Matrix ι ι ℂ))ᴴ * (R * (U : Matrix ι ι ℂ)))
      ((R * (U : Matrix ι ι ℂ))ᴴ * L * (R * (U : Matrix ι ι ℂ))) =
      hessianCost (Rᴴ * R) (Rᴴ * L * R) := by
  simpa only [conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      hessianCost_unitary_conj (star U) (Matrix.posSemidef_conjTranspose_mul_self R)
        (Rᴴ * L * R)

def phaseEdge (z : ℂ) (W : Three → Matrix ι ι ℂ) : Three → Matrix ι ι ℂ :=
  fun v => if v = 0 then z • W 0 else W v

def rowPhase (z : ℂ) (v : Three) : BlockSpace ι → ℂ := fun a =>
  if v = 0 then (if a.1 = 1 then z else 1)
  else if v = 1 then (if a.1 = 0 then star z else 1) else 1

omit [Fintype ι] [DecidableEq ι] in
theorem rowPhase_norm (z : ℂ) (hz : ‖z‖ = 1) (v : Three) (a : BlockSpace ι) :
    ‖rowPhase z v a‖ = 1 := by
  unfold rowPhase
  split_ifs <;> simp [hz]

theorem rowStar_phase (z : ℂ) (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (phaseEdge z W) v = rowStar W v * Matrix.diagonal (rowPhase z v) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases v <;> fin_cases a <;> fin_cases b
  all_goals simp [rowStar, vertexProj, triangle, Matrix.comp_apply,
    triangleBlocks, phaseEdge, rowPhase, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, smul_eq_mul, mul_comm]

theorem starCost_phase (z : ℂ) (hz : ‖z‖ = 1)
    (W D : Three → Matrix ι ι ℂ) (v : Three) :
    hessianCost (starGram (phaseEdge z W) v) (starInsert (phaseEdge z W) D v) =
      hessianCost (starGram W v) (starInsert W D v) := by
  let U := diagonalUnitary (rowPhase (ι := ι) z v) (rowPhase_norm z hz v)
  have he : rowStar (phaseEdge z W) v = rowStar W v * (U : Matrix _ _ ℂ) :=
    rowStar_phase z W v
  simp only [starGram, starInsert, he]
  exact insertedCost_right_unitary (rowStar W v) (blockD D) U

omit [Fintype ι] [DecidableEq ι] in
theorem exists_phase_norm (τ : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ z * τ = (‖τ‖ : ℂ) := by
  by_cases hτ : τ = 0
  · exact ⟨1, norm_one, by simp [hτ]⟩
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.mpr hτ
  have hnc : (‖τ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  refine ⟨star τ / (‖τ‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      (star τ / (‖τ‖ : ℂ)) * τ = (τ * star τ) / (‖τ‖ : ℂ) := by ring
      _ = (‖τ‖ : ℂ)^2 / (‖τ‖ : ℂ) := by rw [RCLike.star_def, Complex.mul_conj']
      _ = _ := by field_simp

theorem mixed_trace_le (W D : Three → Matrix ι ι ℂ)
    (hD : ∀ v, (D v).IsHermitian) :
    ‖Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)‖ ≤
      (5 / 3 : ℝ) * ‖blockD D‖ * ∑ v, hessianCost (starGram W v) (starInsert W D v) := by
  let τ := Matrix.trace (D 0 * W 0 * D 1 * W 1 * D 2 * W 2)
  obtain ⟨z, hz, he⟩ := exists_phase_norm τ
  have ht : Matrix.trace (D 0 * phaseEdge z W 0 * D 1 *
      phaseEdge z W 1 * D 2 * phaseEdge z W 2) = z * τ := by
    simp [phaseEdge, τ]
  have h := triangle_real_trace_le (phaseEdge z W) D hD
  rw [ht, he] at h
  simp only [Complex.ofReal_re, abs_of_nonneg (norm_nonneg τ)] at h
  simpa only [starCost_phase z hz] using h

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def regularize (P : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ := P + η • 1

omit [Fintype ι] in
theorem regularize_posDef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (regularize P η).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

omit [Fintype ι] in
theorem regularize_posSemidef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) : (regularize P η).PosSemidef :=
  hP.add (Matrix.PosSemidef.one.smul hη)

theorem continuous_sqrt_matrix {X : Type uX} [TopologicalSpace X]
    {P : X → Matrix ι ι ℂ} (hP : _root_.Continuous P)
    (hn : ∀ x, (P x).PosSemidef) : _root_.Continuous (fun x => CFC.sqrt (P x)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun x => (hn x).nonneg)

theorem continuous_energyGram : _root_.Continuous
    (fun R : Matrix ι ι ℂ => energy (Rᴴ * R)) := by
  unfold energy
  exact traceRealCLM.continuous.comp
    ((continuous_star.mul continuous_id).mul
      (continuous_sqrt_matrix (continuous_star.mul continuous_id)
        Matrix.posSemidef_conjTranspose_mul_self))

theorem energy_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy (conjStarAlgAut ℂ _ U P) = energy P := by
  have hs : CFC.sqrt (conjStarAlgAut ℂ _ U P) =
      conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
    · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
          (U : Matrix ι ι ℂ)).nonneg
  simp only [energy, hs, ← map_mul, traceReal_unitary_conj]

theorem sqrt_diagonal_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    CFC.sqrt (Matrix.diagonal (fun i => (q i : ℂ))) =
      Matrix.diagonal (fun i => ((Real.sqrt (q i) : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact_mod_cast (Real.mul_self_sqrt (hq i))
  · exact (Matrix.PosSemidef.diagonal (fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))).nonneg

theorem energy_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    energy (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, q i * Real.sqrt (q i) := by
  simp [energy, sqrt_diagonal_nonneg q hq, Matrix.diagonal_mul_diagonal, traceReal]

theorem energy_spectral {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P = ∑ i, hP.isHermitian.eigenvalues i * Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [← energy_unitary_conj (star hP.isHermitian.eigenvectorUnitary) hP,
    hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  exact energy_diagonal _ hP.eigenvalues_nonneg

theorem energy_eq_of_charpoly_eq {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P.charpoly = Q.charpoly) :
    energy P = energy Q := by
  rw [energy_spectral hP, energy_spectral hQ,
    (hP.isHermitian.eigenvalues_eq_eigenvalues_iff hQ.isHermitian).mpr hPQ]

theorem energy_gram_flip (R : Matrix ι ι ℂ) : energy (Rᴴ * R) = energy (R * Rᴴ) :=
  energy_eq_of_charpoly_eq (Matrix.posSemidef_conjTranspose_mul_self R)
    (Matrix.posSemidef_self_mul_conjTranspose R) (Matrix.charpoly_mul_comm _ _)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma gradient_gram (R D A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceReal (A * (Rᴴ * D + Dᴴ * R)) = 2 * hsReal (R * A) D := by
  have he : traceReal (A * (Dᴴ * R)) = traceReal (A * (Rᴴ * D)) := by
    rw [traceReal_mul_comm, ← traceReal_star (Dᴴ * R * A)]
    simp only [Matrix.conjTranspose_mul, hA.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  simp only [hsReal, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc,
    mul_add, traceReal_add, he]
  ring

lemma energyGradient_gram (P R D : Matrix ι ι ℂ) :
    energyGradient P (Rᴴ * D + Dᴴ * R) =
      3 * hsReal (R * CFC.sqrt P) D := by
  have hs : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  rw [energyGradient_apply, gradient_gram R D (CFC.sqrt P) hs]
  ring

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hsReal_nonneg_of_posSemidef {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ hsReal X Y := by
  let B := CFC.sqrt Y
  have hB : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)).isHermitian
  have hBB : B * B = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hn := traceReal_nonneg (hX.conjTranspose_mul_mul_same B)
  rw [hB.eq, traceReal_mul_cycle, hBB, traceReal_mul_comm] at hn
  simpa only [hsReal, hX.isHermitian.eq] using hn

omit [DecidableEq ι] in
lemma sylv_star {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (Y : Matrix ι ι ℂ) :
    sylv A Yᴴ = (sylv A Y)ᴴ := by
  simp only [sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hA.eq]
  exact add_comm _ _

lemma sylv_solution_isHermitian {A K Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (hY : sylv A Y = K) : Y.IsHermitian := by
  change Yᴴ = Y
  apply (sylvEquiv hA).injective
  change sylv A Yᴴ = sylv A Y
  rw [sylv_star hA.isHermitian, hY, hK.eq]

lemma posSemidef_of_sylv_posSemidef {A Y : Matrix ι ι ℂ} (hA : A.PosDef)
    (hY : Y.IsHermitian) (hS : (sylv A Y).PosSemidef) : Y.PosSemidef := by
  apply hY.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hY.eigenvalues i
  let U := hY.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hD : f Y = Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)) :=
    hY.conjStarAlgAut_star_eigenvectorUnitary
  have hAf : (f A).PosDef := by
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe (U := star U))).mpr hA
  have hSf : (f (sylv A Y)).PosSemidef := by
    exact hS.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have he : f (sylv A Y) = sylv (f A) (f Y) :=
    (sylv_unitary_conj (star U) A Y).symm
  rw [he, hD] at hSf
  have hn : 0 ≤ (sylv (f A) (Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ))) i i).re :=
    (RCLike.nonneg_iff.mp hSf.diag_nonneg).1
  have hp : 0 < (f A i i).re := (RCLike.pos_iff.mp hAf.diag_pos).1
  simp only [sylv, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] at hn
  nlinarith

lemma rootCost_le_of_order_posDef {A K : Matrix ι ι ℂ} (hA : A.PosDef)
    (hK : K.IsHermitian) (c : ℝ)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  let Y := (sylvEquiv hA).symm K
  have hY : sylv A Y = K := (sylvEquiv hA).apply_symm_apply K
  have hYh : Y.IsHermitian := sylv_solution_isHermitian hA hK hY
  let Z : Matrix ι ι ℂ := (c / 2) • A
  have hZ : sylv A Z = c • (A * A) := by
    change A * ((c / 2) • A) + ((c / 2) • A) * A = _
    rw [Matrix.mul_smul, Matrix.smul_mul, ← add_smul]
    congr 1
    ring
  have hYZ : (Z + Y).PosSemidef := by
    apply posSemidef_of_sylv_posSemidef hA
      ((hA.isHermitian.smul (show IsSelfAdjoint (c / 2) from rfl)).add hYh)
    rwa [sylv_add_right, hZ, hY]
  have hn := hsReal_nonneg_of_posSemidef hm hYZ
  have hc : hsReal (sylv A Z) Y = hsReal K Z := by
    rw [← hsReal_sylv_symm hA.isHermitian, hY, hsReal_symm]
  have hb : hsReal K Y ≤ hsReal (sylv A Z) Z := by
    rw [← hZ, hsReal_sub_left, hsReal_add_right, hsReal_add_right, hc] at hn
    linarith
  rw [rootCost_eq_of_solution hA.posSemidef hY]
  calc
    _ ≤ (3 / 2 : ℝ) * hsReal (sylv A Z) Z := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
      rw [hZ]
      change (3 / 2 : ℝ) * hsReal (c • (A * A)) ((c / 2) • A) = _
      rw [hsReal_smul_left, hsReal_smul_right]
      simp only [hsReal, Matrix.conjTranspose_mul, hA.isHermitian.eq]
      ring

lemma regularize_square (A : Matrix ι ι ℂ) (δ : ℝ) :
    regularize A δ * regularize A δ = A * A + (2 * δ) • A + δ^2 • 1 := by
  simp only [regularize, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
    one_mul, mul_one, smul_smul]
  module

lemma regularize_square_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ) : A * A ≤ regularize A δ * regularize A δ := by
  rw [regularize_square, add_assoc]
  exact le_add_of_nonneg_right
    (((hA.smul (mul_nonneg (by norm_num) hδ)).add
      (Matrix.PosSemidef.one.smul (sq_nonneg δ))).nonneg)

omit [DecidableEq ι] in
lemma continuous_variation_left (K X : Matrix ι ι ℂ) :
    Continuous (fun A : Matrix ι ι ℂ => variation A K X) := by
  exact continuous_const.sub (traceRealCLM.continuous.comp
    (continuous_const.mul ((continuous_id.mul continuous_const).add
      (continuous_const.mul continuous_id))))

theorem rootCost_le_of_order {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hK : K.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hm : (c • (A * A) - K).PosSemidef)
    (hp : (c • (A * A) + K).PosSemidef) :
    rootCost A K ≤ (3 / 4 : ℝ) * c^2 * traceReal (A * A * A) := by
  have hb (δ : ℝ) (hδ : 0 < δ) (X : Matrix ι ι ℂ) :
      (3 / 2 : ℝ) * variation (regularize A δ) K X ≤
        (3 / 4 : ℝ) * c^2 * traceReal (regularize A δ * regularize A δ * regularize A δ) := by
    have hd := regularize_posDef hA hδ
    have ho := smul_le_smul_of_nonneg_left (regularize_square_le hA hδ.le) hc
    have hmd : (c • (regularize A δ * regularize A δ) - K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hm.nonneg.trans (sub_le_sub_right ho K))
    have hpd : (c • (regularize A δ * regularize A δ) + K).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (hp.nonneg.trans (add_le_add ho le_rfl))
    exact (variation_le_rootCost hd.posSemidef (exists_sylv_solution_posDef hd K) X).trans
      (rootCost_le_of_order_posDef hd hK c hmd hpd)
  have hv (X : Matrix ι ι ℂ) : variation A K X ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    have hAc : Continuous (regularize A) := by unfold regularize; fun_prop
    have hf : Continuous (fun δ => (3 / 2 : ℝ) * variation (regularize A δ) K X) :=
      continuous_const.mul ((continuous_variation_left K X).comp hAc)
    have hg : Continuous (fun δ => (3 / 4 : ℝ) * c^2 *
        traceReal (regularize A δ * regularize A δ * regularize A δ)) :=
      continuous_const.mul (traceRealCLM.continuous.comp ((hAc.mul hAc).mul hAc))
    have hl := le_of_tendsto_of_tendsto
      (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 _))
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), _ from by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hb δ hδ X)
    simp only [regularize, zero_smul, add_zero] at hl
    linarith
  have hs : sSup (Set.range (variation A K)) ≤ (1 / 2 : ℝ) * c^2 * traceReal (A * A * A) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    exact hv X
  unfold rootCost
  nlinarith

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    hessianCost (Rᴴ * R) (Rᴴ * L * R) ≤
      (3 / 4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : (CFC.sqrt (Rᴴ * R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have hAA : CFC.sqrt (Rᴴ * R) * CFC.sqrt (Rᴴ * R) = Rᴴ * R :=
    CFC.sqrt_mul_sqrt_self (Rᴴ * R) hP.nonneg
  have hb : L ≤ ‖L‖ • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).le_algebraMap_norm_self
  have ha : -(‖L‖ • (1 : Matrix ι ι ℂ)) ≤ L := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint L from hL).neg_algebraMap_norm_le_self
  have hm : (‖L‖ • (Rᴴ * R) - Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one] using
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hb)).conjTranspose_mul_mul_same R
  have hp : (‖L‖ • (Rᴴ * R) + Rᴴ * L * R).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, add_comm] using
      (Matrix.nonneg_iff_posSemidef.mp (neg_le_iff_add_nonneg.mp ha)).conjTranspose_mul_mul_same R
  unfold hessianCost
  simpa only [hAA, energy] using rootCost_le_of_order hA
    (by
      change (Rᴴ * L * R)ᴴ = Rᴴ * L * R
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL.eq, Matrix.mul_assoc]) (norm_nonneg L) (by simpa [hAA] using hm)
      (by simpa [hAA] using hp)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma blockD_mul (A B : Three → Matrix ι ι ℂ) :
    blockD A * blockD B = blockD (fun v => A v * B v) := by
  unfold blockD
  rw [← blocks_mul, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] [DecidableEq ι] in
lemma blockD_star (A : Three → Matrix ι ι ℂ) :
    (blockD A)ᴴ = blockD (fun v => (A v)ᴴ) := by
  unfold blockD
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  rfl

lemma blockD_posSemidef (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) : (blockD A).PosSemidef := by
  have he : blockD A = (blockD (fun v => CFC.sqrt (A v)))ᴴ *
      blockD (fun v => CFC.sqrt (A v)) := by
    rw [blockD_star, blockD_mul]
    congr 1
    funext v
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma sqrt_blockD (A : Three → Matrix ι ι ℂ) (hA : ∀ v, (A v).PosSemidef) :
    CFC.sqrt (blockD A) = blockD (fun v => CFC.sqrt (A v)) := by
  apply CFC.sqrt_unique
  · rw [blockD_mul]
    congr 1
    funext v
    exact CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg
  · exact (blockD_posSemidef _ (fun v =>
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v)))).nonneg

omit [DecidableEq ι] in
lemma hsReal_blocks_blockD (K : Matrix Three Three (Matrix ι ι ℂ))
    (Y : Three → Matrix ι ι ℂ) :
    hsReal (blocks K) (blockD Y) = ∑ v, hsReal (K v v) (Y v) := by
  simp only [hsReal, blockD, ← blocks_star, ← blocks_mul, traceReal, blocks_trace,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Complex.re_sum]

omit [DecidableEq ι] in
lemma sylv_blockD (A Y : Three → Matrix ι ι ℂ) :
    sylv (blockD A) (blockD Y) = blockD (fun v => sylv (A v) (Y v)) := by
  unfold sylv
  rw [blockD_mul, blockD_mul]
  unfold blockD
  change (Matrix.compRingEquiv Three ι ℂ) _ + (Matrix.compRingEquiv Three ι ℂ) _ =
    (Matrix.compRingEquiv Three ι ℂ) _
  rw [← map_add, ← Matrix.diagonal_add]

lemma rootCost_blockD_ge_diagonal (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) (K : Matrix Three Three (Matrix ι ι ℂ))
    (hsol : ∃ Y, sylv (blockD A) Y = blocks K)
    (hdiag : ∀ v, ∃ Y, sylv (A v) Y = K v v) :
    ∑ v, rootCost (A v) (K v v) ≤ rootCost (blockD A) (blocks K) := by
  choose Y hY using hdiag
  have hv := variation_le_rootCost (blockD_posSemidef A hA) hsol (blockD Y)
  have he : variation (blockD A) (blocks K) (blockD Y) =
      ∑ v, hsReal (K v v) (Y v) := by
    rw [variation, penalty, sylv_blockD]
    simp only [hY]
    rw [hsReal_blocks_blockD]
    change 2 * (∑ v, hsReal (K v v) (Y v)) -
      hsReal (blocks (Matrix.diagonal Y)) (blockD (fun v => K v v)) = _
    rw [hsReal_blocks_blockD, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [Matrix.diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro v _
    rw [hsReal_symm (Y v) (K v v)]
    ring
  rw [he] at hv
  simp_rw [rootCost_eq_of_solution (hA _) (hY _)]
  simpa only [Finset.mul_sum] using hv

theorem hessianCost_le_of_le_smul {P Q K : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K)
    {c : ℝ} (hc : 0 < c) (hPQ : P ≤ c • Q) :
    hessianCost Q K ≤ Real.sqrt c * hessianCost P K := by
  have hr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hAs : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hps : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hsolc := sylv_solvable_mono hps
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (c • Q))).isHermitian hsol
      (CFC.monotone_sqrt hPQ)
  rw [sqrt_smul hQ hc.le] at hsolc
  have hsolQ : ∃ Y, sylv (CFC.sqrt Q) Y = K := by
    obtain ⟨Y, hY⟩ := hsolc
    refine ⟨Real.sqrt c • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hm := hessianCost_antitone hsol hPQ
  change rootCost (CFC.sqrt (c • Q)) K ≤ rootCost (CFC.sqrt P) K at hm
  rw [sqrt_smul hQ hc.le, rootCost_scale hAs hsolQ hr] at hm
  have hx := mul_le_mul_of_nonneg_left hm hr.le
  simpa only [hessianCost, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hx

def wideRow (R : Three → Matrix ι ι ℂ) : Matrix ι (BlockSpace ι) ℂ :=
  fun i a => R a.1 i a.2

def gramRow (R : Three → Matrix ι ι ℂ) := blocks (fun i j => (R i)ᴴ * R j)
def insertRow (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :=
  blocks (fun i j => (R i)ᴴ * L * R j)
def pinchedRow (R : Three → Matrix ι ι ℂ) := blockD (fun v => (R v)ᴴ * R v)

omit [DecidableEq ι] in
lemma gramRow_eq (R : Three → Matrix ι ι ℂ) : gramRow R = (wideRow R)ᴴ * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma insertRow_eq (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :
    insertRow R L = (wideRow R)ᴴ * L * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma gramRow_posSemidef (R : Three → Matrix ι ι ℂ) : (gramRow R).PosSemidef := by
  rw [gramRow_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma pinchedRow_posSemidef (R : Three → Matrix ι ι ℂ) : (pinchedRow R).PosSemidef :=
  blockD_posSemidef _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)

lemma gramRow_le_two_pinchedRow (R : Three → Matrix ι ι ℂ)
    (v : Three) (hR : R v = 0) : gramRow R ≤ (2 : ℝ) • pinchedRow R := by
  let R' : Three → Matrix ι ι ℂ := fun i => if i = v + 1 then R i else -(R i)
  have he : (2 : ℝ) • pinchedRow R - gramRow R = gramRow R' := by
    ext a b
    rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    change (2 : ℝ) • (Matrix.diagonal (fun k => (R k)ᴴ * R k) a b i j) -
      ((R a)ᴴ * R b) i j = ((R' a)ᴴ * R' b) i j
    fin_cases v
    · change R 0 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 1 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 2 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
  rw [Matrix.le_iff, he]
  exact gramRow_posSemidef R'

theorem hessianCost_gramRow_ge_edges (R : Three → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (v : Three) (hR : R v = 0) :
    (∑ w, hessianCost ((R w)ᴴ * R w) ((R w)ᴴ * L * R w)) ≤
      Real.sqrt 2 * hessianCost (gramRow R) (insertRow R L) := by
  have hsol : ∃ Y, sylv (CFC.sqrt (gramRow R)) Y = insertRow R L := by
    rw [gramRow_eq, insertRow_eq]
    exact sylv_solvable_inserted_gram _ _
  have hQ := pinchedRow_posSemidef R
  have hle := gramRow_le_two_pinchedRow R v hR
  have hqs : (CFC.sqrt (pinchedRow R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (pinchedRow R))
  have hsol2 := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramRow R)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((2 : ℝ) • pinchedRow R))).isHermitian
    hsol (CFC.monotone_sqrt hle)
  rw [sqrt_smul hQ (by norm_num : (0 : ℝ) ≤ 2)] at hsol2
  have hsolQ : ∃ Y, sylv (CFC.sqrt (pinchedRow R)) Y = insertRow R L := by
    obtain ⟨Y, hY⟩ := hsol2
    refine ⟨Real.sqrt 2 • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hdiag (w : Three) := sylv_solvable_inserted_gram (R w) L
  have hs : CFC.sqrt (pinchedRow R) = blockD (fun w => CFC.sqrt ((R w)ᴴ * R w)) :=
    sqrt_blockD _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hl := rootCost_blockD_ge_diagonal
    (fun w => CFC.sqrt ((R w)ᴴ * R w))
    (fun w => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((R w)ᴴ * R w)))
    (fun i j => (R i)ᴴ * L * R j) (by simpa only [← hs, insertRow] using hsolQ) hdiag
  calc
    _ ≤ hessianCost (pinchedRow R) (insertRow R L) := by
      simpa only [hessianCost, hs, insertRow] using hl
    _ ≤ _ := hessianCost_le_of_le_smul hQ hsol (by norm_num : (0 : ℝ) < 2) hle

lemma rowStar_blocks (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v = blocks (fun a b => if a = v then triangleBlocks W a b else 0) := by
  ext a b
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  simp only [rowStar, vertexProj, Matrix.diagonal_mul, triangle, blocks, Matrix.comp_apply]
  change (if a = v then (1 : ℂ) else 0) * triangleBlocks W a b i j =
    (if a = v then triangleBlocks W a b else 0) i j
  split_ifs <;> simp

lemma starGram_eq_gramRow (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = gramRow (triangleBlocks W v) := by
  unfold starGram
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks A = _
  rw [← blocks_star, ← blocks_mul]
  unfold gramRow
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, star (A c a) * A c b) = (triangleBlocks W v a)ᴴ * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

lemma starInsert_eq_insertRow (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = insertRow (triangleBlocks W v) (D v) := by
  unfold starInsert blockD
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks (Matrix.diagonal D) * blocks A = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold insertRow
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  change (∑ c, star (A c a) * D c * A c b) =
    (triangleBlocks W v a)ᴴ * D v * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

def centerGram (W : Three → Matrix ι ι ℂ) (v : Three) : Matrix ι ι ℂ :=
  ∑ w, triangleBlocks W v w * (triangleBlocks W v w)ᴴ

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_adj (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W v w)ᴴ = triangleBlocks W w v := by
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks]

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_diag (W : Three → Matrix ι ι ℂ) (v : Three) :
    triangleBlocks W v v = 0 := by
  fin_cases v <;> simp [triangleBlocks]

omit [DecidableEq ι] in
lemma centerGram_posSemidef (W : Three → Matrix ι ι ℂ) (v : Three) :
    (centerGram W v).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun w _ => (Matrix.posSemidef_self_mul_conjTranspose _).nonneg)

omit [DecidableEq ι] in
lemma edgeGram_le_centerGram (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W w v)ᴴ * triangleBlocks W w v ≤ centerGram W v := by
  rw [triangleBlocks_adj]
  rw [← triangleBlocks_adj W v w]
  exact Finset.single_le_sum (fun a _ =>
    (Matrix.posSemidef_self_mul_conjTranspose (triangleBlocks W v a)).nonneg)
    (Finset.mem_univ w)

theorem neighbor_comparison (W D : Three → Matrix ι ι ℂ) (w : Three) :
    (∑ v, hessianCost (centerGram W v)
      ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v)) ≤
      Real.sqrt 2 * hessianCost (starGram W w) (starInsert W D w) := by
  rw [starGram_eq_gramRow, starInsert_eq_insertRow]
  calc
    _ ≤ ∑ v, hessianCost ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)
        ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v) := by
      apply Finset.sum_le_sum
      intro v _
      exact hessianCost_antitone (sylv_solvable_inserted_gram _ _)
        (edgeGram_le_centerGram W v w)
    _ ≤ _ := hessianCost_gramRow_ge_edges _ (D w) w (triangleBlocks_diag W w)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def sqrtInverse {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm

lemma sqrtInverse_solves {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    sylv (CFC.sqrt P) (sqrtInverse hP K) = K := by
  exact (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).apply_symm_apply K

def hessianPairPD {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) : ℝ :=
  (3 / 2 : ℝ) * hsReal K (sqrtInverse hP L)

lemma hessianPairPD_symm {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    hessianPairPD hP K L = hessianPairPD hP L K := by
  have hs := hsReal_sylv_symm
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
    (sqrtInverse hP K) (sqrtInverse hP L)
  rw [sqrtInverse_solves, sqrtInverse_solves, hsReal_symm _ L] at hs
  exact congrArg ((3 / 2 : ℝ) * ·) hs.symm

lemma hessianPairPD_self {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    hessianPairPD hP K K = hessianCost P K := by
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) (sqrtInverse_solves hP K)).symm

lemma two_hessianPairPD_le {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    2 * hessianPairPD hP K L ≤ hessianCost P K + hessianCost P L := by
  have hn := rootCost_nonneg (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P))
    (show ∃ Y, sylv (CFC.sqrt P) Y = K - L from ⟨_, sqrtInverse_solves hP (K - L)⟩)
  change 0 ≤ hessianCost P (K - L) at hn
  rw [← hessianPairPD_self hP] at hn
  have he : hessianPairPD hP (K - L) (K - L) =
      hessianPairPD hP K K + hessianPairPD hP L L - 2 * hessianPairPD hP K L := by
    have hs := hessianPairPD_symm hP K L
    simp only [hessianPairPD, map_sub, hsReal_sub_left, hsReal_sub_right] at *
    linarith
  rw [he, hessianPairPD_self, hessianPairPD_self] at hn
  linarith

lemma hessianPairPD_eq_trace {P K L : Matrix ι ι ℂ}
    (hP : P.PosDef) (hK : K.IsHermitian) :
    hessianPairPD hP K L = (3 / 2 : ℝ) * traceReal (sqrtInverse hP L * K) := by
  simp only [hessianPairPD, hsReal, hK.eq, traceReal_mul_comm K]

theorem energy_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ} {U : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t) (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  exact (energy_hasFDerivWithinAt hP).comp_hasDerivAt x hd hn

theorem energyGradient_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {U V : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t)
    (hK : (K x).IsHermitian) (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPairPD hP (K x) U + energyGradient (P x) V) x := by
  have hs : HasDerivAt (fun t => CFC.sqrt (P t)) (sqrtInverse hP U) x :=
    (sqrt_smoothWithin_posDef hP).2.comp_hasDerivAt x hdP hn
  have hm := hs.fun_mul hdK
  have ht := (traceRealCLM.hasFDerivAt.comp_hasDerivAt x hm).const_smul (3 / 2 : ℝ)
  convert! ht using 1
  simp only [hessianPairPD_eq_trace hP hK, energyGradient_apply,
    traceRealCLM_apply, traceReal_add, smul_eq_mul]
  ring

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

def rowNorm (R : Matrix ι κ ℂ) (i : ι) : ℝ := Real.sqrt (∑ j, ‖R i j‖^2)
def colNorm (R : Matrix ι κ ℂ) (j : κ) : ℝ := Real.sqrt (∑ i, ‖R i j‖^2)

omit [Fintype ι] [Fintype μ] in
theorem norm_mul_entry_le (R : Matrix ι κ ℂ) (S : Matrix κ μ ℂ) (i : ι) (j : μ) :
    ‖(R * S) i j‖ ≤ rowNorm R i * colNorm S j := by
  calc
    ‖(R * S) i j‖ ≤ ∑ k, ‖R i k * S k j‖ := norm_sum_le _ _
    _ = ∑ k, ‖R i k‖ * ‖S k j‖ := by simp only [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

omit [Fintype κ] in
theorem colNorm_sq (R : Matrix ι κ ℂ) (j : κ) :
    (colNorm R j)^2 = ((Rᴴ * R) j j).re := by
  rw [colNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable [DecidableEq κ]

theorem colNorm_sqrt_gram (R : Matrix ι κ ℂ) (j : κ) :
    colNorm (CFC.sqrt (Rᴴ * R)) j = colNorm R j := by
  have hsP := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Rᴴ * R))
  have he : (colNorm (CFC.sqrt (Rᴴ * R)) j)^2 = (colNorm R j)^2 := by
    rw [colNorm_sq, hsP.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (Rᴴ * R) (Matrix.posSemidef_conjTranspose_mul_self R).nonneg,
      colNorm_sq]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp he

theorem entry_gradient_le (R : Matrix ι κ ℂ) (i : ι) (j : κ) :
    ‖(R * CFC.sqrt (Rᴴ * R)) i j‖ ≤ rowNorm R i * colNorm R j := by
  simpa only [colNorm_sqrt_gram] using norm_mul_entry_le R (CFC.sqrt (Rᴴ * R)) i j

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI
