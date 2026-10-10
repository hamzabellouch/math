import OAI.NumberTheory.JointDickman.Arithmetic.BrunTruncation
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

/-! # An exponential error bound for even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_error (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) ≤ (if S = ∅ then 1 else 0) + (4 : ℝ)^S.card/(4 : ℝ)^r := by
  classical
  rw [brunTruncation_even]
  by_cases hS : S = ∅
  · simp only [hS, ite_true, card_empty, pow_zero]
    have h : 0 ≤ (1 : ℝ)/4^r := by positivity
    linarith
  · simp only [hS, ite_false, zero_add]
    by_cases hcard : S.card ≤ 2*r
    · have hlt : S.card-1 < 2*r := by
        have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
        omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      positivity
    · have hcr : 2*r ≤ S.card := by omega
      have hchoose : ((S.card-1).choose (2*r) : ℝ) ≤ (2 : ℝ)^(S.card-1) := by
        exact_mod_cast Nat.choose_le_two_pow (S.card-1) (2*r)
      apply hchoose.trans
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4^r)).mpr
      calc
        (2 : ℝ)^(S.card-1)*4^r = 2^(S.card-1+2*r) := by
          rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_add]
        _ ≤ 2^(2*S.card) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4^S.card := by rw [show (4 : ℝ) = 2^2 by norm_num, pow_mul]

noncomputable def brunMean (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ E ∈ P.powerset, bernoulliSubsetMass P g E * brunTruncation E (2*r)

 theorem brunMean_le (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) {B : ℝ} (hB : ∑ p ∈ P, g p ≤ B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4 : ℝ)^r := by
  classical
  have he : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (if E = ∅ then 1 else 0)) =
      ∏ p ∈ P, (1-g p) := by
    rw [sum_eq_single ∅]
    · simp [bernoulliSubsetMass]
    · intro E _ hE
      simp [hE]
    · simp
  have hm : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (4 : ℝ)^E.card) =
      ∏ p ∈ P, (1+3*g p) := by
    simpa only [prod_const, show ∀ p, 1-g p+g p*4 = 1+3*g p by intro p; ring] using
      bernoulliSubsetMass_tilt P g (fun _ => 4)
  have hp : (∏ p ∈ P, (1+3*g p)) ≤ Real.exp (3*B) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (3*g p) := prod_le_prod₀
        (fun p hp => by linarith [(hg p hp).1])
        (fun p _ => by simpa only [add_comm] using Real.add_one_le_exp (3*g p))
      _ = Real.exp (3*∑ p ∈ P, g p) := by rw [mul_sum, Real.exp_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∑ E ∈ P.powerset, bernoulliSubsetMass P g E *
        ((if E = ∅ then 1 else 0)+(4 : ℝ)^E.card/(4 : ℝ)^r) := by
      apply sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_left (brunTruncation_error E r)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    _ = (∏ p ∈ P, (1-g p)) + (∏ p ∈ P, (1+3*g p))/(4 : ℝ)^r := by
      simp only [mul_add, ← mul_div_assoc, sum_add_distrib, ← sum_div, he, hm]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hp (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) r))

end JointDickman

end OAI
