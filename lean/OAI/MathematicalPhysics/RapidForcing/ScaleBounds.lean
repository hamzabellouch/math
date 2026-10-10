import OAI.MathematicalPhysics.RapidForcing.Scales

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing
namespace ScaleData

lemma weighted_geometric_summable (J : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ J * (1 / 2 : ℝ) ^ n) := by
  have h := (summable_nat_add_iff 3).mpr
    (summable_pow_mul_geometric_of_norm_lt_one J (r := (1 / 2 : ℝ)) (by norm_num))
  apply (h.mul_left (8 : ℝ)).congr
  intro n
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add]
  norm_num
  ring

variable (d : ScaleData)

lemma scaled_b_le_delta (n p : ℕ) (h : p + 1 ≤ n + 10) :
    d.b n / d.δ n ^ p ≤ d.δ n := by
  apply (div_le_iff₀ (pow_pos (d.delta_pos n) p)).mpr
  calc
    d.b n ≤ d.δ n ^ (n + 10) := d.b_le_delta_pow n
    _ ≤ d.δ n ^ (p + 1) := pow_le_pow_of_le_one (d.delta_nonneg n) (d.delta_le_one n) h
    _ = d.δ n * d.δ n ^ p := pow_succ' _ _

lemma scaled_b_sq_le_delta (n p : ℕ) (h : p + 1 ≤ 2 * (n + 10)) :
    d.b n ^ 2 / d.δ n ^ p ≤ d.δ n := by
  apply (div_le_iff₀ (pow_pos (d.delta_pos n) p)).mpr
  calc
    d.b n ^ 2 ≤ (d.δ n ^ (n + 10)) ^ 2 :=
      pow_le_pow_left₀ (d.b_pos n).le (d.b_le_delta_pow n) 2
    _ = d.δ n ^ (2 * (n + 10)) := by rw [← pow_mul, Nat.mul_comm (n + 10)]
    _ ≤ d.δ n ^ (p + 1) := pow_le_pow_of_le_one (d.delta_nonneg n) (d.delta_le_one n) h
    _ = d.δ n * d.δ n ^ p := pow_succ' _ _

lemma residual_coefficient_le {n p : ℕ} (h : p ≤ n) :
    d.b n / d.δ n ^ (p + 2) + d.b n ^ 2 / d.δ n ^ (p + 1) ≤ 2 * d.δ n := by
  have h₁ := d.scaled_b_le_delta n (p + 2) (by omega)
  have h₂ := d.scaled_b_sq_le_delta n (p + 1) (by omega)
  linarith

lemma velocity_coefficient_summable (J p : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ J * (d.b n / d.δ n ^ p)) := by
  apply (summable_nat_add_iff p).mp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_nat_add_iff p).mpr (weighted_geometric_summable J))
  · exact mul_nonneg (by positivity)
      (div_nonneg (d.b_pos _).le (pow_nonneg (d.delta_nonneg _) _))
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (d.scaled_b_le_delta _ _ (by omega)).trans (d.delta_le_geometric _)

lemma residual_coefficient_summable (J p : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ J *
      (d.b n / d.δ n ^ (p + 2) + d.b n ^ 2 / d.δ n ^ (p + 1))) := by
  apply (summable_nat_add_iff p).mp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_nat_add_iff p).mpr ((weighted_geometric_summable J).mul_left 2))
  · have hb := d.b_pos (n + p)
    have hδ := d.delta_pos (n + p)
    positivity
  · calc
      _ ≤ (((n + p : ℕ) : ℝ) + 3) ^ J * (2 * d.δ (n + p)) :=
        mul_le_mul_of_nonneg_left (d.residual_coefficient_le (by omega)) (by positivity)
      _ ≤ (((n + p : ℕ) : ℝ) + 3) ^ J * (2 * (1 / 2 : ℝ) ^ (n + p)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (d.delta_le_geometric _) (by norm_num)) (by positivity)
      _ = _ := by ring

theorem velocity_coefficient_bound (J p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ((n : ℝ) + 3) ^ J * (d.b n / d.δ n ^ p) ≤ C := by
  let a := fun n : ℕ => ((n : ℝ) + 3) ^ J * (d.b n / d.δ n ^ p)
  have ha : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg (by positivity) (div_nonneg (d.b_pos _).le (pow_nonneg (d.delta_nonneg _) _))
  refine ⟨∑' n : ℕ, a n, tsum_nonneg ha, ?_⟩
  intro n
  exact (d.velocity_coefficient_summable J p).le_tsum n (fun j _ => ha j)

theorem residual_coefficient_bound (J p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ((n : ℝ) + 3) ^ J *
        (d.b n / d.δ n ^ (p + 2) + d.b n ^ 2 / d.δ n ^ (p + 1)) ≤ C := by
  let a := fun n : ℕ => ((n : ℝ) + 3) ^ J *
    (d.b n / d.δ n ^ (p + 2) + d.b n ^ 2 / d.δ n ^ (p + 1))
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    have hb := d.b_pos n
    have hδ := d.delta_pos n
    dsimp [a]
    positivity
  refine ⟨∑' n : ℕ, a n, tsum_nonneg ha, ?_⟩
  intro n
  exact (d.residual_coefficient_summable J p).le_tsum n (fun j _ => ha j)

end ScaleData
end RapidForcing

end OAI
