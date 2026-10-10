import OAI.NumberTheory.JointDickman.Counting.PeriodicAverages

namespace OAI

/-! # Nonnegative periodic sums with a bound for one complete period -/
namespace JointDickman
open Finset

lemma residue_real_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ x : ZMod q, f x) = ∑ n ∈ range q, f (n:ZMod q) := by
  apply Complex.ofReal_injective
  push_cast
  exact residue_sum_eq_range (fun x => (f x:ℂ))

lemma periodic_real_sum_div_mod {q : ℕ} (f : ZMod q → ℝ) (L : ℕ) :
    (∑ n ∈ range L, f (n:ZMod q)) = ((L/q:ℕ):ℝ) *
      (∑ n ∈ range q, f (n:ZMod q)) + ∑ n ∈ range (L%q), f (n:ZMod q) := by
  apply Complex.ofReal_injective
  push_cast
  exact periodic_sum_div_mod (fun x => (f x:ℂ)) L

lemma periodic_nonnegative_prefix_bound {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hf : ∀ x, 0 ≤ f x) {A : ℝ} (hA : 0 ≤ A)
    (hperiod : (∑ x : ZMod q, f x) ≤ (q:ℝ)*A) (L : ℕ) :
    (∑ n ∈ range L, f (n:ZMod q)) ≤ ((L:ℝ)+q)*A := by
  rw [periodic_real_sum_div_mod]
  have hrem : (∑ n ∈ range (L%q), f (n:ZMod q)) ≤ ∑ n ∈ range q, f (n:ZMod q) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mod_lt L (NeZero.pos q)).le)
      (fun n _ _ => hf _)
  have hdiv : ((L/q:ℕ):ℝ)*(q:ℝ) ≤ L := by exact_mod_cast Nat.div_mul_le_self L q
  have hp : (∑ n ∈ range q, f (n:ZMod q)) ≤ (q:ℝ)*A := by
    rw [←residue_real_sum_eq_range]
    exact hperiod
  calc
    _ ≤ ((L/q:ℕ):ℝ)*(∑ n ∈ range q, f (n:ZMod q)) +
        ∑ n ∈ range q, f (n:ZMod q) := add_le_add le_rfl hrem
    _ = (((L/q:ℕ):ℝ)+1)*(∑ n ∈ range q, f (n:ZMod q)) := by ring
    _ ≤ (((L/q:ℕ):ℝ)+1)*((q:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hdiv hA]

end JointDickman

end OAI
