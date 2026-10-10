import OAI.NumberTheory.JointDickman.Probability.GraphResidueFactors
import OAI.NumberTheory.JointDickman.Amplification.ActiveVolumeMajorant

namespace OAI

/-! # Removing coefficient primes from the three quotient weights -/

namespace JointDickman
open Finset

theorem graph_residue_product {K : Type*} [Field K]
    (a b c j m l₁ l₂ n : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hn : n = b*l₁) (hj : n+j = a*l₂) (hm : c*n = a*b*m+b) :
    residueWeight (1/2) 0 m * residueWeight (1/2) 0 l₁ * residueWeight (1/2) 0 l₂ =
      residueWeight (1/2) 0 n * residueWeight (1/2) (-j) n *
        residueWeight (1/2) (b/c) n := by
  classical
  have h₁ : l₁ = 0 ↔ n = 0 := by
    rw [hn, mul_eq_zero]
    simp [hb]
  have h₂ : l₂ = 0 ↔ n = -j := by
    rw [← add_eq_zero_iff_eq_neg, hj, mul_eq_zero]
    simp [ha]
  have h₃ : m = 0 ↔ n = b/c := by
    rw [eq_div_iff hc]
    constructor
    · intro h
      rw [h, mul_zero, zero_add] at hm
      simpa only [mul_comm] using hm
    · intro h
      have hz : a*b*m = 0 := by linear_combination -hm + h
      exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ha hb)
  simp only [residueWeight, h₁, h₂, h₃]
  ring

open Classical in
theorem base_residue_three_subset_le (B : ℕ) (G : Finset ℕ)
    (hG : G ⊆ auxiliaryPrimes B) (m l₁ l₂ : ℕ) :
    baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ ≤
    (auxiliaryRatio B ^ (1/2 : ℝ))^3 *
      ∏ p ∈ G, (if p ∣ m then (1/2 : ℝ) else 1) *
        (if p ∣ l₁ then (1/2 : ℝ) else 1) *
        (if p ∣ l₂ then (1/2 : ℝ) else 1) := by
  let f (p : ℕ) := (if p ∣ m then (1/2 : ℝ) else 1) *
    (if p ∣ l₁ then (1/2 : ℝ) else 1) * (if p ∣ l₂ then (1/2 : ℝ) else 1)
  have hf0 (p : ℕ) : 0 ≤ f p := by dsimp [f]; positivity
  have hf1 (p : ℕ) : f p ≤ 1 := by
    dsimp [f]
    split_ifs <;> norm_num
  have he : baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ =
      (auxiliaryRatio B ^ (1/2 : ℝ))^3 * ∏ p ∈ auxiliaryPrimes B, f p := by
    simp only [baseArithmeticResidueWeight_product, f, prod_mul_distrib]
    ring
  rw [he]
  have hR : 0 ≤ auxiliaryRatio B := by unfold auxiliaryRatio; positivity
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.rpow_nonneg hR _) _)
  exact prod_le_prod_of_subset_of_le_one₀ hG (fun p _ => hf0 p) (fun p _ _ => hf1 p)

open Classical in
/-- An exact congruence calculation turns the retained quotient factors
into the three distinct roots used in the edge-mass calculation. -/
theorem graph_quotient_residue_majorant (B : ℕ) (G : Finset ℕ)
    (hG : G ⊆ auxiliaryPrimes B) (a b c m l₁ l₂ n : ℕ) (j : ℤ)
    (ha : ∀ p ∈ G, ¬ p ∣ a) (hb : ∀ p ∈ G, ¬ p ∣ b) (hc : ∀ p ∈ G, ¬ p ∣ c)
    (hn : n = b*l₁) (hj : (n : ℤ)+j = a*l₂) (hm : c*n = a*b*m+b) :
    baseArithmeticResidueWeight B m * baseArithmeticResidueWeight B l₁ *
      baseArithmeticResidueWeight B l₂ ≤
      (auxiliaryRatio B ^ (1/2 : ℝ))^3 * ∏ p ∈ G,
        residueWeight (1/2) (0 : ZMod p) (n : ZMod p) *
        residueWeight (1/2) (-(j : ZMod p)) (n : ZMod p) *
        residueWeight (1/2) ((b : ZMod p)*(c : ZMod p)⁻¹) (n : ZMod p) := by
  apply (base_residue_three_subset_le B G hG m l₁ l₂).trans_eq
  congr 1
  apply prod_congr rfl
  intro p hp
  let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p (hG hp)⟩
  have hne (x : ℕ) (hx : ¬ p ∣ x) : (x : ZMod p) ≠ 0 := by
    exact fun h => hx ((ZMod.natCast_eq_zero_iff x p).mp h)
  have hn' : (n : ZMod p) = (b : ZMod p)*(l₁ : ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod p)) hn
  have hj' : (n : ZMod p)+(j : ZMod p) = (a : ZMod p)*(l₂ : ZMod p) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ZMod p)) hj
  have hm' : (c : ZMod p)*(n : ZMod p) =
      (a : ZMod p)*(b : ZMod p)*(m : ZMod p)+(b : ZMod p) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using congrArg (fun x : ℕ => (x : ZMod p)) hm
  have h := graph_residue_product (a : ZMod p) b c j m l₁ l₂ n
    (hne a (ha p hp)) (hne b (hb p hp)) (hne c (hc p hp)) hn' hj' hm'
  simpa only [residueWeight, ZMod.natCast_eq_zero_iff, div_eq_mul_inv] using h

end JointDickman

end OAI
