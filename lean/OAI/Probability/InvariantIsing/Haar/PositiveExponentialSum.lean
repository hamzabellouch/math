import OAI.Probability.InvariantIsing.Haar.HaarPolynomialEntropyBound

namespace OAI

/-! Monotone positive truncations of the scalar exponential series. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def positiveExpSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), x^k/(Nat.factorial k : ℝ)

lemma positiveExpSum_one_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ positiveExpSum n x := by
  have h := Finset.single_le_sum
    (f := fun k => x^k/(Nat.factorial k : ℝ))
    (fun k (_ : k ∈ Finset.range (n+1)) => div_nonneg (pow_nonneg hx k) (Nat.cast_nonneg _))
    (show 0 ∈ Finset.range (n+1) by simp)
  simpa only [positiveExpSum,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using h

lemma positiveExpSum_mono (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    positiveExpSum n x ≤ positiveExpSum (n+1) x := by
  unfold positiveExpSum
  conv_rhs => rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))

lemma positiveExpSum_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    positiveExpSum n x ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx (n+1)

lemma positiveExpSum_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => positiveExpSum n x) atTop (𝓝 (Real.exp x)) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).tendsto_sum_nat
  have hh := h.comp (tendsto_add_atTop_nat 1)
  simpa only [positiveExpSum,Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_comm,
    Real.exp_eq_exp_ℝ] using hh

end InvariantIsing

end

end OAI
