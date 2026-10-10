import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearBound

namespace OAI

/-! # The exact split of a product divisor between coprime coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisor_split_unique {d n₁ n₂ e : ℕ} (_hd : d ≠ 0)
    (hcop : n₁.Coprime n₂) (he : e ∣ d) (h₁ : e ∣ n₁) (h₂ : d / e ∣ n₂) :
    e = d.gcd n₁ := by
  have hcross : (d / e).Coprime n₁ := hcop.symm.of_dvd_left h₂
  have hg := Nat.gcd_mul_of_coprime_of_dvd hcross h₁
  simpa only [Nat.div_mul_cancel he] using hg.symm

 theorem quadratic_divisor_split_exists {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) (hdiv : d ∣ n₁ * n₂) :
    d.gcd n₁ ∈ d.divisors ∧ d.gcd n₁ ∣ n₁ ∧ d / d.gcd n₁ ∣ n₂ := by
  have hprod : d.gcd n₁ * d.gcd n₂ = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdiv
  have hg : 0 < d.gcd n₁ := Nat.gcd_pos_of_pos_left n₁ hd
  have heq : d / d.gcd n₁ = d.gcd n₂ := by
    exact Nat.div_eq_of_eq_mul_left hg (by simpa only [Nat.mul_comm] using hprod.symm)
  exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hd.ne'⟩,
    Nat.gcd_dvd_right _ _, heq ▸ Nat.gcd_dvd_right d n₂⟩

 theorem quadratic_product_divisor_indicator {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) :
    (if d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
      ∑ e ∈ d.divisors, if e ∣ n₁ ∧ d / e ∣ n₂ then (1 : ℂ) else 0 := by
  by_cases hdiv : d ∣ n₁ * n₂
  · obtain ⟨he, h₁, h₂⟩ := quadratic_divisor_split_exists hd hcop hdiv
    rw [ite_eq_left hdiv, Finset.sum_eq_single (d.gcd n₁)]
    · rw [ite_eq_left ⟨h₁, h₂⟩]
    · intro e he' hne
      apply ite_eq_right
      intro hh
      exact hne (quadratic_divisor_split_unique hd.ne' hcop
        (Nat.dvd_of_mem_divisors he') hh.1 hh.2)
    · exact fun hn => (hn he).elim
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro e he
    apply ite_eq_right
    intro hh
    have hp := Nat.mul_dvd_mul hh.1 hh.2
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)] at hp
    exact hdiv hp

noncomputable def quadraticDivisorBilinear (N₁ N₂ d : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
    (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) *
      a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)

 theorem quadratic_divisor_bilinear_split (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ e ∈ d.divisors, quadraticCoprimeBilinear N₁ N₂
        (fun n => if e ∣ n then a n else 0)
        (fun n => if d / e ∣ n then b n else 0) m := by
  have hp (n₁ n₂ : ℕ) :
      (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ e ∈ d.divisors, (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    by_cases hc : n₁.Coprime n₂
    · simp_rw [ite_eq_left hc, one_mul]
      have hi : (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
          (if d ∣ n₁ * n₂ then 1 else 0) := by
        by_cases hx : d ∣ n₁ * n₂ <;> simp [hc, hx]
      rw [hi, quadratic_product_divisor_indicator hd hc]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h₁ : e ∣ n₁ <;> by_cases h₂ : d / e ∣ n₂ <;> simp [h₁, h₂]
    · simp [hc]
  unfold quadraticDivisorBilinear
  simp_rw [hp]
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ e ∈ d.divisors,
        ∑ n₂ ∈ oddSquarefreeRange N₂,
          (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
            (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
            (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

end Ostmann

end OAI
