import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337
/-- Only prime sample values which divide the modulus contribute to the gcd.
The index set, unlike a set of prime values, retains repeated samples. -/
theorem prime_gcd_eq_hit_gcd {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u =
      Nat.gcd (∏ i ∈ s with p i ∣ u, p i) u := by
  classical
  have hcop : Nat.Coprime (∏ i ∈ s with ¬ p i ∣ u, p i) u := by
    apply Nat.Coprime.prod_left
    intro i hi
    obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
    exact (hp i his).coprime_iff_not_dvd.mpr hnot
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => p i ∣ u) p]
  exact hcop.gcd_mul_right_cancel _

theorem prime_gcd_dvd_hit_product {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s with p i ∣ u, p i := by
  classical
  rw [prime_gcd_eq_hit_gcd s p u hp]
  exact Nat.gcd_dvd_left _ _

theorem prime_gcd_le_hit_product {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u ≤ ∏ i ∈ s with p i ∣ u, p i := by
  classical
  apply Nat.le_of_dvd _ (prime_gcd_dvd_hit_product s p u hp)
  exact Finset.prod_pos (fun i hi => (hp i (Finset.mem_filter.mp hi).1).pos)

theorem prime_gcd_le_pow_hit_count {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u B : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) (hB : ∀ i ∈ s, p i ≤ B) :
    Nat.gcd (∏ i ∈ s, p i) u ≤ B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  calc
    Nat.gcd (∏ i ∈ s, p i) u ≤ ∏ i ∈ s with p i ∣ u, p i :=
      prime_gcd_le_hit_product s p u hp
    _ ≤ ∏ _i ∈ s with p _i ∣ u, B :=
      Finset.prod_le_prod (fun i hi => hB i (Finset.mem_filter.mp hi).1)
    _ = B ^ (s.filter (fun i => p i ∣ u)).card := by simp

/-- Real-valued sample bounds are convenient when the sampling interval is
specified by a real asymptotic parameter. -/
theorem prime_gcd_le_real_pow_hit_count {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) (B : ℝ) (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hB : ∀ i ∈ s, (p i : ℝ) ≤ B) :
    (Nat.gcd (∏ i ∈ s, p i) u : ℝ) ≤
      B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  calc
    (Nat.gcd (∏ i ∈ s, p i) u : ℝ) ≤ (∏ i ∈ s with p i ∣ u, p i : ℕ) := by
      exact_mod_cast prime_gcd_le_hit_product s p u hp
    _ = ∏ i ∈ s with p i ∣ u, (p i : ℝ) := by push_cast; rfl
    _ ≤ ∏ _i ∈ s with p _i ∣ u, B := by
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        exact hB i (Finset.mem_filter.mp hi).1
    _ = B ^ (s.filter (fun i => p i ∣ u)).card := by simp

/-- A large gcd forces many hits, counted with their sample multiplicities. -/
theorem hit_count_large_of_gcd_large {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) {B x : ℝ} (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hB : ∀ i ∈ s, (p i : ℝ) ≤ B) (hB1 : 1 < B) (hx : 0 < x)
    (hlarge : x < (Nat.gcd (∏ i ∈ s, p i) u : ℝ)) :
    Real.log x / Real.log B < ((s.filter (fun i => p i ∣ u)).card : ℝ) := by
  classical
  have hlt := hlarge.trans_le (prime_gcd_le_real_pow_hit_count s p u B hp hB)
  have hlog := Real.log_lt_log hx hlt
  rw [Real.log_pow] at hlog
  exact (div_lt_iff₀ (Real.log_pos hB1)).2 hlog

end Problem337

end

end OAI
