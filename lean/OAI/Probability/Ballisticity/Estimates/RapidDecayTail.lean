import Mathlib
import OAI.Probability.Ballisticity.Estimates.RapidDecay

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.summable {a : ℕ → ℝ} (ha : RapidDecay a) : Summable a := by
  simpa using ha 0

lemma RapidDecay.tail {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n) :
    RapidDecay (fun n => ∑' k, a (n+k)) := by
  intro m
  let T := ∑' k : ℕ, (k+1:ℝ)^(m+2)*a k
  have ht (n : ℕ) : Summable (fun k => a (n+k)) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).mpr ha.summable
  have hbound (n : ℕ) : (n+1:ℝ)^(m+2)*(∑' k, a (n+k)) ≤ T := by
    rw [← (ht n).tsum_mul_left]
    have hshift : Summable (fun k : ℕ => (n+k+1:ℝ)^(m+2)*a (n+k)) := by
      simpa only [Nat.cast_add,add_comm (n:ℝ),Nat.add_comm n] using (summable_nat_add_iff n).mpr (ha (m+2))
    calc
      _ ≤ ∑' k : ℕ, (n+k+1:ℝ)^(m+2)*a (n+k) := by
        apply (ht n |>.mul_left _).tsum_le_tsum _ hshift
        intro k
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) k]) _) (ha0 _)
      _ ≤ T := by
        have hh := (ha (m+2)).sum_add_tsum_nat_add n
        have hz : 0 ≤ ∑ k ∈ Finset.range n, (k+1:ℝ)^(m+2)*a k :=
          Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (ha0 _))
        simpa only [T,Nat.add_comm n,Nat.cast_add,add_comm (n:ℝ)] using (show
          (∑' k : ℕ, (↑(k+n)+1:ℝ)^(m+2)*a (k+n)) ≤ T by linarith [hh])
  have hs : Summable (fun n : ℕ => T*((n+1:ℝ)^2)⁻¹) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by omega : 1<(2:ℕ)))
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (tsum_nonneg (fun k => ha0 _)))]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℝ)^2)).mpr
  simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using hbound n

end DirectionalTransience

end

end OAI
