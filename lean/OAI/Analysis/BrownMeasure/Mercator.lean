import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def mercator (a : A) : A := -∑' n : ℕ, ((n+1 : ℝ)⁻¹) • a^(n+1)

lemma inv_nat_succ_le_one (n : ℕ) : |(n+1 : ℝ)⁻¹|≤1 := by
  rw [abs_of_pos (inv_pos.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma mercator_summable {a : A} (ha : ‖a‖<1) :
    Summable (fun n : ℕ=>((n+1 : ℝ)⁻¹) • a^(n+1)) := by
  apply (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right ‖a‖ |>.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ 1*‖a^(n+1)‖ := mul_le_mul_of_nonneg_right (inv_nat_succ_le_one n) (norm_nonneg _)
    _ ≤ ‖a‖^n*‖a‖ := by simpa [pow_succ] using norm_pow_le a (n+1)

variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))

omit [CompleteSpace A] [NormOneClass A] in
include hτ in
lemma trace_pow_deriv {f : ℝ → A} {d : A} {x : ℝ} (hf : HasDerivAt f d x) (n : ℕ) :
    HasDerivAt (fun t=>τ (f t^(n+1))) (((n+1:ℝ))*τ (f x^n*d)) x := by
  have hd := τ.hasFDerivAt.comp_hasDerivAt x (hf.fun_pow' (n+1))
  have hsum : τ (∑ i ∈ Finset.range (n+1),f x ^ ((n+1).pred-i)*d*f x^i)=
      ((n+1:ℝ))*τ (f x^n*d) := by
    rw [map_sum]
    have he (i : ℕ) (hi : i∈Finset.range (n+1)) :
        τ (f x ^ ((n+1).pred-i)*d*f x^i)=τ (f x^n*d) := by
      rw [hτ _ (f x^i),← mul_assoc,← pow_add]
      have hi' : i≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
      simp [Nat.add_sub_of_le hi']
    simp_rw [Finset.sum_congr rfl he]
    simp
  simpa only [Function.comp_def,hsum] using hd

lemma trace_mercator_hasSum {a : A} (ha : ‖a‖<1) :
    HasSum (fun n : ℕ=>-((n+1 : ℝ)⁻¹)*τ (a^(n+1))) (τ (mercator a)) := by
  have h := (τ.hasSum (mercator_summable ha).hasSum).neg
  simpa [mercator,map_neg,map_smul,smul_eq_mul] using h
end BrownLog
end

end OAI
