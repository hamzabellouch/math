import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- An integral positive sum divisible by `p` gives a common-denominator
representation of `p`; products of divisors of `P` divide `P²`. -/
theorem rational_divisor_sum_of_divisible {k P p : ℕ} (hk : 0 < k)
    (hp : 0 < p) (a b : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (had : ∀ i, a i ∣ P) (hbd : ∀ i, b i ∣ P)
    (hdiv : p ∣ ∑ i, a i * b i) :
    ∃ t : ℕ, 0 < t ∧ (∀ i, 0 < a i * b i ∧ a i * b i ∣ P ^ 2) ∧
      (p : ℚ) = ∑ i, ((a i * b i : ℕ) : ℚ) / t := by
  have hspos : 0 < ∑ i, a i * b i := by
    exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨⟨0, hk⟩,
      Finset.mem_univ _, Nat.mul_pos (ha _) (hb _)⟩
  obtain ⟨t, hsum⟩ := hdiv
  have ht : 0 < t := by
    rw [hsum] at hspos
    by_contra h
    have ht0 : t = 0 := by omega
    simp [ht0] at hspos
  refine ⟨t, ht, ?_, ?_⟩
  · intro i
    exact ⟨Nat.mul_pos (ha i) (hb i), by
      simpa only [pow_two] using Nat.mul_dvd_mul (had i) (hbd i)⟩
  · rw [← Finset.sum_div, ← Nat.cast_sum, hsum, Nat.cast_mul]
    field_simp

/-- The preceding lifting lemma can take a modular zero-sum directly. -/
theorem rational_divisor_sum_of_zmod_zero {k P p : ℕ} (hk : 0 < k)
    (hp : 0 < p) (a b : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (had : ∀ i, a i ∣ P) (hbd : ∀ i, b i ∣ P)
    (hzero : (∑ i, (a i : ZMod p) * (b i : ZMod p)) = 0) :
    ∃ t : ℕ, 0 < t ∧ (∀ i, 0 < a i * b i ∧ a i * b i ∣ P ^ 2) ∧
      (p : ℚ) = ∑ i, ((a i * b i : ℕ) : ℚ) / t := by
  apply rational_divisor_sum_of_divisible hk hp a b ha hb had hbd
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_sum, Nat.cast_mul] using hzero

/-- Lift products of residue classes represented by positive divisors. -/
theorem rational_divisor_sum_of_residue_products {k P p : ℕ}
    (hk : 0 < k) (hp : 0 < p) (x y : Fin k → ZMod p)
    (hx : ∀ i, x i ∈ P.divisors.image (fun a : ℕ => (a : ZMod p)))
    (hy : ∀ i, y i ∈ P.divisors.image (fun a : ℕ => (a : ZMod p)))
    (hsum : (∑ i, x i * y i) = 0) :
    ∃ e : Fin k → ℕ, ∃ t : ℕ, 0 < t ∧
      (∀ i, 0 < e i ∧ e i ∣ P ^ 2) ∧
      (p : ℚ) = ∑ i, (e i : ℚ) / t := by
  have hx' : ∀ i, ∃ a : ℕ, a ∈ P.divisors ∧ (a : ZMod p) = x i := by
    intro i
    exact Finset.mem_image.mp (hx i)
  have hy' : ∀ i, ∃ b : ℕ, b ∈ P.divisors ∧ (b : ZMod p) = y i := by
    intro i
    exact Finset.mem_image.mp (hy i)
  choose a ha hax using hx'
  choose b hb hby using hy'
  have hz : (∑ i, (a i : ZMod p) * (b i : ZMod p)) = 0 := by
    simpa only [hax, hby] using hsum
  obtain ⟨t, ht, he, hrep⟩ := rational_divisor_sum_of_zmod_zero hk hp a b
    (fun i => Nat.pos_of_mem_divisors (ha i))
    (fun i => Nat.pos_of_mem_divisors (hb i))
    (fun i => Nat.dvd_of_mem_divisors (ha i))
    (fun i => Nat.dvd_of_mem_divisors (hb i)) hz
  exact ⟨fun i => a i * b i, t, ht, he, hrep⟩

end Problem337

end

end OAI
