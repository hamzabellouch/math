import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorSplit

namespace OAI

/-! # Splitting the small-kernel conductor divisors into the fixed and pair parts -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_coprime_divisor_sum {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (F : ℕ → ℂ) :
    (∑ d ∈ (m * n).divisors, F d) =
      ∑ e ∈ m.divisors, ∑ f ∈ n.divisors, F (e * f) := by
  symm
  rw [← Finset.sum_product m.divisors n.divisors (fun z => F (z.1 * z.2))]
  have hleft (z : ℕ × ℕ) (hz : z ∈ m.divisors.product n.divisors) :
      z.1 = (z.1 * z.2).gcd m := by
    obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
    have he := Nat.pos_of_mem_divisors hz₁
    have hf := Nat.pos_of_mem_divisors hz₂
    apply quadratic_divisor_split_unique (Nat.mul_pos he hf).ne' hcop
      (dvd_mul_right z.1 z.2) (Nat.dvd_of_mem_divisors hz₁)
    simpa only [Nat.mul_div_cancel_left _ he] using Nat.dvd_of_mem_divisors hz₂
  apply Finset.sum_bij (fun z _ => z.1 * z.2)
  · intro z hz
    obtain ⟨he, hf⟩ := Finset.mem_product.mp hz
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors he)
      (Nat.dvd_of_mem_divisors hf), (Nat.mul_pos hm hn).ne'⟩
  · intro z hz w hw heq
    have hfst : z.1 = w.1 := by rw [hleft z hz, hleft w hw, heq]
    have hz₀ : z.1 ≠ 0 := (Nat.pos_of_mem_divisors (Finset.mem_product.mp hz).1).ne'
    have hsnd : z.2 = w.2 := by
      rw [← hfst] at heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hz₀) heq
    exact Prod.ext hfst hsnd
  · intro d hd
    have hd₀ := Nat.pos_of_mem_divisors hd
    obtain ⟨he, hem, hfn⟩ := quadratic_divisor_split_exists hd₀ hcop (Nat.dvd_of_mem_divisors hd)
    refine ⟨(d.gcd m, d / d.gcd m), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨hem, hm.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨hfn, hn.ne'⟩
    · exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
  · intro z _
    rfl

end Ostmann

end OAI
