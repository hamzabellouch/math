import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentProducts
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.Nilpotent.Exp

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Nilpotence truncates the analytic exponential exactly. -/
theorem exp_eq_finite_sum_of_pow_eq_zero (x : A) {c : ℕ} (hx : x ^ c = 0) :
    NormedSpace.exp x = ∑ k ∈ Finset.range c, ((k.factorial : ℝ)⁻¹) • x ^ k := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  apply tsum_eq_sum
  intro k hk
  have hck : c ≤ k := by simpa using hk
  rw [pow_eq_zero_of_le hck hx, smul_zero]

/-- The polynomial exponential gives a uniform increment bound on any fixed
bounded set of nilpotent logarithms. -/
theorem norm_exp_sub_one_le_of_pow_eq_zero [NormOneClass A]
    (x : A) {c : ℕ} (hx : x ^ (c + 1) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ‖x‖ ≤ M) :
    ‖NormedSpace.exp x - 1‖ ≤ (c : ℝ) * (1 + M) ^ c := by
  rw [exp_eq_finite_sum_of_pow_eq_zero x hx, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖((k + 1).factorial : ℝ)⁻¹ • x ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + M) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hi : ‖((k + 1).factorial : ℝ)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ = ‖((k + 1).factorial : ℝ)⁻¹‖ * ‖x ^ (k + 1)‖ := norm_smul _ _
        _ ≤ 1 * ‖x ^ (k + 1)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ ≤ (1 + M) ^ (k + 1) := by
          rw [one_mul]
          exact (norm_pow_le _ _).trans
            (pow_le_pow_left₀ (norm_nonneg _) (by linarith) (k + 1))
        _ ≤ (1 + M) ^ c := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hk)
    _ = _ := by simp

end Algebra

section Matrix

open scoped Matrix.Norms.Operator

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem StrictUpper.pow {X : Matrix (Fin n) (Fin n) ℝ} (hX : StrictUpper X)
    {k : ℕ} (hk : 0 < k) : StrictUpper (X ^ k) := by
  intro i j hij
  have hlist : ∀ A ∈ List.replicate k X, StrictUpper A := by
    intro A hA
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hA
    exact hX
  have hentry := strictUpper_prod_entry_zero (List.replicate k X) hlist i j (by
    simp only [List.length_replicate]
    have hji : (j : ℕ) ≤ i := hij
    omega)
  simpa only [List.prod_replicate] using hentry

omit [NeZero n] in
theorem StrictUpper.exp_sub_one {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : StrictUpper X) : StrictUpper (NormedSpace.exp X - 1) := by
  have hpow : X ^ (n + 1) = 0 := by
    have := strictUpper_prod_zero (List.replicate (n + 1) X)
      (fun A hA => by obtain ⟨_, rfl⟩ := List.mem_replicate.mp hA; exact hX) (by simp)
    simpa only [List.prod_replicate] using this
  have hexp : NormedSpace.exp X =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) • X ^ k := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    apply tsum_eq_sum
    intro k hk
    rw [pow_eq_zero_of_le (by simpa using hk) hpow, smul_zero]
  rw [hexp, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  intro i j hij
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [hX.pow (Nat.succ_pos k) i j hij, mul_zero]

/-- Ordered products of actual matrix exponentials of bounded strictly upper
triangular logarithms satisfy a polynomial bound, uniformly in word length. -/
theorem norm_prod_exp_strictUpper_le
    (l : List (Matrix (Fin n) (Fin n) ℝ)) (hl : ∀ X ∈ l, StrictUpper X)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ X ∈ l, ‖X‖ ≤ M) :
    ‖(l.map NormedSpace.exp).prod‖ ≤
      (n : ℝ) * (1 + (n : ℝ) * (1 + M) ^ n) ^ n * (1 + (l.length : ℝ)) ^ n := by
  let q : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun X => NormedSpace.exp X - 1
  have hq : ∀ Y ∈ l.map q, StrictUpper Y := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
    exact (hl X hX).exp_sub_one
  have hb : ∀ Y ∈ l.map q, ‖Y‖ ≤ (n : ℝ) * (1 + M) ^ n := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
    have hpow : X ^ (n + 1) = 0 := by
      simpa only [List.prod_replicate] using strictUpper_prod_zero
        (List.replicate (n + 1) X)
        (fun A hA => by
          have heq : A = X := (List.mem_replicate.mp hA).2
          rw [heq]
          exact hl X hX)
        (by simp)
    exact norm_exp_sub_one_le_of_pow_eq_zero X hpow hM (hbound X hX)
  have h := norm_unipotent_prod_le (l.map q) hq (by positivity) hb
  have heq : ((l.map q).map (fun A => 1 + A)) = l.map NormedSpace.exp := by
    rw [List.map_map]
    apply List.map_congr_left
    intro X _
    dsimp [q]
    abel
  simpa only [heq, List.length_map] using h

end Matrix
end PolycyclicRecognition

end OAI
