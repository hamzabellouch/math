import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinatePacking
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-!
# Packing matrix regions in a left invariant group metric

A local metric bound near the identity converts separation into separation of
matrix coordinates. Polynomial bounds on matrices and their inverses therefore
produce polynomially many integer grid labels. The local metric bound remains
explicit so it can be supplied by the actual Lie-group chart.
-/

namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator NNReal

variable {n : ℕ}

theorem matrix_entry_norm_le (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => ∑ l, ‖A k l‖₊) (Finset.mem_univ i))
  exact_mod_cast h

theorem matrix_norm_le_of_entries (A : Matrix (Fin n) (Fin n) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ M) : ‖A‖ ≤ (n : ℝ) * M := by
  let m : ℝ≥0 := ⟨M, hM⟩
  have h : ‖A‖₊ ≤ (n : ℝ≥0) * m := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc
      ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, m := by
        apply Finset.sum_le_sum
        intro j _
        exact_mod_cast hA i j
      _ = _ := by simp
  exact_mod_cast h

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

omit [IsIsometricSMul G G] in
/-- The local metric bound follows from a genuine matrix embedding. -/
theorem exists_local_matrix_metric_bound
    (ρ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hρ : Topology.IsInducing (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g,
      ‖(ρ g : Matrix (Fin n) (Fin n) ℝ) - 1‖ ≤ ε → dist 1 g ≤ 1 := by
  have hb : Metric.ball (1 : G) 1 ∈ nhds (1 : G) := Metric.ball_mem_nhds _ (by norm_num)
  rw [hρ.nhds_eq_comap] at hb
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hb
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨ε / 2, by positivity, fun g hg => ?_⟩
  have hdist : dist (ρ g : Matrix (Fin n) (Fin n) ℝ)
      (ρ 1 : Matrix (Fin n) (Fin n) ℝ) < ε := by
    rw [map_one, Units.val_one, dist_eq_norm]
    exact lt_of_le_of_lt hg (by linarith)
  have hmem := hsub (hball hdist)
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_comm] using hmem)

omit [IsIsometricSMul G G] in
/-- Properness and continuity bound all step matrices of a fixed metric size. -/
theorem exists_bounded_step_matrices [ProperSpace G]
    (ρ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hρ : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ))) (L : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g, dist 1 g ≤ L → ‖(ρ g : Matrix (Fin n) (Fin n) ℝ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (1 : G) L).exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun g hg => ?_⟩
  apply (hM g ?_).trans (le_max_right _ _)
  simpa only [Metric.mem_closedBall, dist_comm] using hg

/-- Metric separation forces one matrix coordinate difference at the scale
predicted by the inverse-matrix bound. -/
theorem exists_separated_matrix_entry
    (ρ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ) {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q)
    (hlocal : ∀ g, ‖(ρ g : Matrix (Fin n) (Fin n) ℝ) - 1‖ ≤ ε → dist 1 g ≤ 1)
    (x y : G) (hxy : 1 < dist x y)
    (hinv : ‖(↑(ρ x)⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤ Q) :
    ∃ i j, ε / (Q * ((n : ℝ) + 1)) ≤
      |(ρ x : Matrix (Fin n) (Fin n) ℝ) i j - (ρ y : Matrix (Fin n) (Fin n) ℝ) i j| := by
  by_contra hno
  push Not at hno
  let δ := ε / (Q * ((n : ℝ) + 1))
  have hden : 0 < Q * ((n : ℝ) + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hd : ‖(ρ y : Matrix (Fin n) (Fin n) ℝ) - (ρ x : Matrix (Fin n) (Fin n) ℝ)‖ ≤
      (n : ℝ) * δ := by
    apply matrix_norm_le_of_entries _ hδ.le
    intro i j
    simpa only [Matrix.sub_apply, Real.norm_eq_abs, abs_sub_comm] using (hno i j).le
  have hnum : Q * ((n : ℝ) * δ) ≤ ε := by
    have hmul : δ * (Q * ((n : ℝ) + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith [mul_pos hQ hδ]
  have heq : (ρ (x⁻¹ * y) : Matrix (Fin n) (Fin n) ℝ) - 1 =
      (↑(ρ x)⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
        ((ρ y : Matrix (Fin n) (Fin n) ℝ) - (ρ x : Matrix (Fin n) (Fin n) ℝ)) := by
    simp only [map_mul, map_inv, Units.val_mul, mul_sub, Units.inv_mul]
  have hb : ‖(ρ (x⁻¹ * y) : Matrix (Fin n) (Fin n) ℝ) - 1‖ ≤ ε := by
    rw [heq]
    exact ((norm_mul_le _ _).trans
      (mul_le_mul hinv hd (norm_nonneg _) hQ.le)).trans hnum
  have hm := hlocal (x⁻¹ * y) hb
  have hdist : dist 1 (x⁻¹ * y) = dist x y := by
    simpa only [mul_one, mul_inv_cancel_left] using (dist_mul_left x 1 (x⁻¹ * y)).symm
  rw [hdist] at hm
  exact (not_le_of_gt hxy) hm

/-- An explicit finite packing bound for regions with controlled matrices and
inverses. No volume or measurability of the endpoint set is assumed. -/
theorem matrix_packing_bound (ρ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ)
    {ε P Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q)
    (hlocal : ∀ g, ‖(ρ g : Matrix (Fin n) (Fin n) ℝ) - 1‖ ≤ ε → dist 1 g ≤ 1)
    (s : Finset G)
    (hmat : ∀ g ∈ s, ‖(ρ g : Matrix (Fin n) (Fin n) ℝ)‖ ≤ P)
    (hinv : ∀ g ∈ s, ‖(↑(ρ g)⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤ Q)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 < dist x y) :
    s.card ≤ (2 * ⌈P / (ε / (Q * ((n : ℝ) + 1)))⌉₊ + 1) ^ (n * n) := by
  have hδ : 0 < ε / (Q * ((n : ℝ) + 1)) := by positivity
  have h := card_le_scaled_grid s
    (fun g (ij : Fin n × Fin n) => (ρ g : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2)
    hδ ⌈P / (ε / (Q * ((n : ℝ) + 1)))⌉₊ (Nat.le_ceil _)
    (by intro x hx ij; exact (matrix_entry_norm_le _ _ _).trans (hmat x hx))
    (by
      intro x hx y hy hxy
      obtain ⟨i, j, hij⟩ := exists_separated_matrix_entry ρ hε hQ hlocal x y
        (hsep x hx y hy hxy) (hinv x hx)
      exact ⟨(i, j), hij⟩)
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

/-- Polynomial bounds for matrix coordinates and inverse coordinates give a
polynomial packing bound, with a fixed degree independent of the finite set. -/
theorem exists_polynomial_matrix_packing
    (ρ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ) {ε A B : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hB : 0 < B) (a b : ℕ)
    (hlocal : ∀ g, ‖(ρ g : Matrix (Fin n) (Fin n) ℝ) - 1‖ ≤ ε → dist 1 g ≤ 1) :
    ∃ C d : ℕ, ∀ (t : ℕ) (s : Finset G),
      (∀ g ∈ s, ‖(ρ g : Matrix (Fin n) (Fin n) ℝ)‖ ≤ A * (1 + (t : ℝ)) ^ a) →
      (∀ g ∈ s, ‖(↑(ρ g)⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤ B * (1 + (t : ℝ)) ^ b) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 < dist x y) → s.card ≤ C * (1 + t) ^ d := by
  let D : ℕ := ⌈A * B * ((n : ℝ) + 1) / ε⌉₊
  refine ⟨(2 * D + 1) ^ (n * n), (a + b) * (n * n), ?_⟩
  intro t s hs hi hsep
  have ht : 0 < 1 + (t : ℝ) := by positivity
  have hQ : 0 < B * (1 + (t : ℝ)) ^ b := mul_pos hB (pow_pos ht _)
  have h := matrix_packing_bound ρ hε hQ hlocal s hs hi hsep
  have heq : (A * (1 + (t : ℝ)) ^ a) /
      (ε / ((B * (1 + (t : ℝ)) ^ b) * ((n : ℝ) + 1))) =
      (A * B * ((n : ℝ) + 1) / ε) * (1 + (t : ℝ)) ^ (a + b) := by
    rw [pow_add]
    field_simp
  have hceil : ⌈(A * (1 + (t : ℝ)) ^ a) /
      (ε / ((B * (1 + (t : ℝ)) ^ b) * ((n : ℝ) + 1)))⌉₊ ≤ D * (1 + t) ^ (a + b) := by
    apply Nat.ceil_le.mpr
    rw [heq]
    have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (A * B * ((n : ℝ) + 1) / ε))
      (pow_nonneg ht.le (a + b))
    simpa only [D, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hc
  have hq : 1 ≤ (1 + t) ^ (a + b) := Nat.one_le_pow _ _ (by omega)
  have hbase : 2 * ⌈(A * (1 + (t : ℝ)) ^ a) /
      (ε / ((B * (1 + (t : ℝ)) ^ b) * ((n : ℝ) + 1)))⌉₊ + 1 ≤
      (2 * D + 1) * (1 + t) ^ (a + b) := by nlinarith
  apply h.trans
  calc
    _ ≤ ((2 * D + 1) * (1 + t) ^ (a + b)) ^ (n * n) :=
      Nat.pow_le_pow_left hbase (n * n)
    _ = _ := by rw [mul_pow, ← pow_mul]

end PolycyclicRecognition

end OAI
