import OAI.NumberTheory.JointDickman.Amplification.LogProductBounds
import OAI.NumberTheory.JointDickman.Arithmetic.TotientLogBound

namespace OAI

/-! # A divisor majorant for the totient correction -/
namespace JointDickman
open Finset

lemma prime_subset_reciprocal_product_le_divisors {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) ≤
      ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  classical
  rw [prod_one_add]
  let e := fun S : Finset ℕ => ∏ p ∈ S, p
  have hi : Set.InjOn e n.primeFactors.powerset := by
    intro S hS T hT he
    change S ∈ n.primeFactors.powerset at hS
    change T ∈ n.primeFactors.powerset at hT
    have hSP := mem_powerset.mp hS
    have hTP := mem_powerset.mp hT
    have hpS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hSP hp)
    have hpT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTP hp)
    have he' := congrArg Nat.primeFactors he
    simpa only [e,Nat.primeFactors_prod hpS,Nat.primeFactors_prod hpT] using he'
  have him : n.primeFactors.powerset.image e ⊆ n.divisors := by
    intro d hd
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨
      (prod_dvd_prod_of_subset S n.primeFactors id (mem_powerset.mp hS)).trans
        (Nat.prod_primeFactors_dvd n),hn.ne'⟩
  apply sum_le_sum_of_injOn e hi him
  · intro S hS
    dsimp [e]
    simp only [Nat.cast_prod,one_div,prod_inv_distrib]
    exact le_rfl
  · intro d hd _
    positivity

lemma totient_ratio_prime_product {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-1/(p:ℝ))⁻¹ := by
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) : 0 < 1-1/(p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : 0 < ∏ p ∈ n.primeFactors, (1-1/(p:ℝ)) := prod_pos hfactor
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [totient_eq_prime_product_real,prod_inv_distrib]
  field_simp

/-- The absolute constant is uniform in n. This is the divisor expansion
needed when summing a rational phase with weight n/φ(n). -/
theorem totient_ratio_le_divisor_reciprocals {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient ≤ Real.exp 2 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  have hp2 (p : ℕ) (hp : p ∈ n.primeFactors) : (2:ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hx (p : ℕ) (hp : p ∈ n.primeFactors) :
      0 ≤ 1/(p:ℝ)^2 ∧ 1/(p:ℝ)^2 ≤ 1/2 := by
    constructor
    · positivity
    · have hp' := hp2 p hp
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ) < p))).mpr
      nlinarith
  have hquad := inverse_product_le_exp n.primeFactors (fun p => 1/(p:ℝ)^2) hx
  have hsum : (∑ p ∈ n.primeFactors, 1/(p:ℝ)^2) ≤ 1 := by
    simpa using sum_reciprocal_square_tail n.primeFactors (N := 1) (by decide)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt)
  have hquad' : (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) ≤ Real.exp 2 :=
    hquad.trans (Real.exp_le_exp.mpr (by linarith))
  have he (p : ℕ) (hp : p ∈ n.primeFactors) :
      (1-1/(p:ℝ))⁻¹ = (1+1/(p:ℝ))*(1-1/(p:ℝ)^2)⁻¹ := by
    have hp' := hp2 p hp
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have h1 : 1-1/(p:ℝ) ≠ 0 := by
      have hh := (div_lt_one (by linarith : (0:ℝ) < p)).mpr (by linarith : (1:ℝ) < p)
      linarith
    have h2 : 1-1/(p:ℝ)^2 ≠ 0 := by linarith [(hx p hp).2]
    have hid : (1-1/(p:ℝ))*(1+1/(p:ℝ)) = 1-1/(p:ℝ)^2 := by
      field_simp
      ring
    rw [←div_eq_mul_inv]
    apply (eq_div_iff h2).mpr
    rw [←hid,←mul_assoc,inv_mul_cancel₀ h1,one_mul]
  rw [totient_ratio_prime_product hn]
  calc
    _ = (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) *
        (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) := by
      rw [←prod_mul_distrib]
      exact prod_congr rfl he
    _ ≤ (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) * Real.exp 2 :=
      mul_le_mul_of_nonneg_left hquad' (prod_nonneg (fun p hp => by positivity))
    _ ≤ Real.exp 2 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (prime_subset_reciprocal_product_le_divisors hn) (Real.exp_pos 2).le

end JointDickman

end OAI
