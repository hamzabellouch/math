import OAI.NumberTheory.Ostmann.Characters.MixedIndicator
import OAI.NumberTheory.Ostmann.Characters.OneSided

namespace OAI

open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

theorem periodic_sum_multiple_zero (f : ℕ → ℂ) {M : ℕ}
    (hper : Function.Periodic f M) (hzero : ∑ i ∈ Finset.range M, f i = 0) (k : ℕ) :
    ∑ i ∈ Finset.range (k*M), f i = 0 := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Nat.succ_mul, Finset.sum_range_add, hk, zero_add]
    have hp (i : ℕ) : f (k*M+i) = f i := by
      simpa only [Nat.cast_id, Nat.add_comm] using hper.nat_mul k i
    simpa only [hp] using hzero

theorem norm_periodic_sum_le (f : ℕ → ℂ) {M : ℕ} (hM : 0 < M)
    (hper : Function.Periodic f M) (hzero : ∑ i ∈ Finset.range M, f i = 0)
    (hbound : ∀ i, ‖f i‖ ≤ 1) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, f i‖ ≤ M := by
  have hp (i : ℕ) : f ((N/M)*M+i) = f i := by
    simpa only [Nat.cast_id, Nat.add_comm] using hper.nat_mul (N/M) i
  have he : ∑ i ∈ Finset.range N, f i = ∑ i ∈ Finset.range (N%M), f i := by
    conv_lhs => rw [← Nat.div_add_mod N M]
    rw [Finset.sum_range_add]
    simp only [Nat.mul_comm M (N/M), periodic_sum_multiple_zero f hper hzero,
      zero_add, hp]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (N%M), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (N%M), (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = (N%M : ℕ) := by simp
    _ ≤ M := by exact_mod_cast (Nat.mod_lt N hM).le

theorem norm_weighted_sum_le {f w : ℕ → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hpartial : ∀ n, ‖∑ i ∈ Finset.range n, f i‖ ≤ C) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, w i * f i‖ ≤
      C * (‖w (N-1)‖ + ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖) := by
  have he := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ ‖w (N-1) * ∑ i ∈ Finset.range N, f i‖ +
        ‖∑ i ∈ Finset.range (N-1), (w (i+1)-w i) *
          ∑ j ∈ Finset.range (i+1), f j‖ := norm_sub_le _ _
    _ ≤ ‖w (N-1)‖ * C +
        ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖ * C := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial N) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial (i+1)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring
end Ostmann.Characters

end OAI
