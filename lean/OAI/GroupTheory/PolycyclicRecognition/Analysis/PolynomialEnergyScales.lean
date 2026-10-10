import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTripling

namespace OAI

/-! # Small relative drops of polynomially bounded-below energy

A positive energy sequence with a polynomial lower bound cannot lose a fixed
positive proportion at every sufficiently late step.
-/
namespace PolycyclicRecognition
open Filter
open scoped Topology

theorem tendsto_nat_add_one_pow_mul_geometric (d : ℕ) {q : ℝ} (hq : 0 < q)
    (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ d * q ^ n) atTop (𝓝 0) := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one d hq.le hq1).comp
    (tendsto_add_atTop_nat 1)
  have ht' := ht.div_const q
  have hfn (n : ℕ) : ((n + 1 : ℕ) : ℝ) ^ d * q ^ (n + 1) / q =
      (1 + (n : ℝ)) ^ d * q ^ n := by
    rw [pow_succ]
    field_simp
    push_cast
    ring
  simpa only [Function.comp_def, hfn, zero_div] using ht'

theorem exists_small_relative_energy_drop (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) {C : ℝ} (hC : 0 < C) (d : ℕ)
    (hlower : ∀ n : ℕ, C ≤ (1 + (n : ℝ)) ^ d * e n)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ n, m ≤ n ∧ e n - e (n + 1) ≤ ε * e n := by
  by_contra! h
  let δ := min ε (1 / 2 : ℝ)
  let q := 1 - δ
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδle : δ ≤ ε := min_le_left _ _
  have hq : 0 < q := by dsimp [q, δ]; linarith [min_le_right ε (1 / 2 : ℝ)]
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hstep (n : ℕ) (hn : m ≤ n) : e (n + 1) ≤ q * e n := by
    have hh := h n hn
    have hd := mul_le_mul_of_nonneg_right hδle (he n)
    dsimp only [q]
    nlinarith
  have hup (k : ℕ) : e (m + k) ≤ q ^ k * e m := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ q * e (m + k) := hstep _ (by omega)
        _ ≤ q * (q ^ k * e m) := mul_le_mul_of_nonneg_left ih hq.le
        _ = _ := by rw [pow_succ]; ring
  have hbound (k : ℕ) : C ≤
      (1 + (m : ℝ)) ^ d * e m * ((1 + (k : ℝ)) ^ d * q ^ k) := by
    calc
      C ≤ (1 + ((m + k : ℕ) : ℝ)) ^ d * e (m + k) := hlower _
      _ ≤ ((1 + (m : ℝ)) * (1 + (k : ℝ))) ^ d * (q ^ k * e m) := by
        apply mul_le_mul _ (hup k) (he _) (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) k)]
      _ = _ := by rw [mul_pow]; ring
  have ht : Tendsto
      (fun k : ℕ => (1 + (m : ℝ)) ^ d * e m * ((1 + (k : ℝ)) ^ d * q ^ k))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_add_one_pow_mul_geometric d hq hq1).const_mul ((1 + (m : ℝ)) ^ d * e m)
  exact (not_le_of_gt hC) (ge_of_tendsto ht (Eventually.of_forall hbound))

end PolycyclicRecognition

end OAI
