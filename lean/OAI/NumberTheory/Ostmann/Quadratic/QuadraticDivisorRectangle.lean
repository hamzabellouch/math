import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorBands

namespace OAI

/-! # The exact finite divisor rectangle underlying the bilinear estimate -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem mem_oddSquarefreeRange_of_dvd {s n N : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (hs : s ∣ n) : s ∈ oddSquarefreeRange N := by
  obtain ⟨hr, ho, hsq⟩ := Finset.mem_filter.mp hn
  have hsm : s ∈ n.divisors := Nat.mem_divisors.mpr ⟨hs, hsq.ne_zero⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.pos_of_mem_divisors hsm, (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hs).trans
      (Finset.mem_Icc.mp hr).2⟩,
    ho.of_dvd_nat hs, hsq.squarefree_of_dvd hs⟩

 theorem quadratic_restricted_bilinear_zero_left {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₁ ∉ oddSquarefreeRange N₁) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ hn₁
  apply Finset.sum_eq_zero
  intro n₂ _
  have hd : ¬s₁ ∣ n₁ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₁ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_zero_right {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₂ ∉ oddSquarefreeRange N₂) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ _
  apply Finset.sum_eq_zero
  intro n₂ hn₂
  have hd : ¬s₂ ∣ n₂ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₂ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_support {N₁ N₂ s₁ s₂ : ℕ}
    (a b : ℕ → ℂ) (m : ℤ)
    (h : quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m ≠ 0) :
    s₁ ∈ oddSquarefreeRange N₁ ∧ s₂ ∈ oddSquarefreeRange N₂ := by
  constructor
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_left hs a b m)
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_right hs a b m)

 theorem quadratic_divisor_bilinear_rectangle (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ z ∈ (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂),
        if z.1 * z.2 = d then quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m else 0 := by
  rw [quadratic_divisor_bilinear_split N₁ N₂ d hd]
  apply Finset.sum_bij_ne_zero (fun e _ _ => (e, d / e))
  · intro e _ he
    exact Finset.mem_product.mpr (quadratic_restricted_bilinear_support a b m he)
  · intro e _ _ f _ _ hef
    exact congrArg Prod.fst hef
  · intro z hz hz0
    have heq : z.1 * z.2 = d := by
      by_contra heq
      simp only [ite_eq_right heq] at hz0
      exact hz0 rfl
    have hzpos : 0 < z.1 :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1).1
    have hdiv : d / z.1 = z.2 :=
      Nat.div_eq_of_eq_mul_left hzpos (by simpa only [mul_comm] using heq.symm)
    refine ⟨z.1, Nat.mem_divisors.mpr ⟨⟨z.2, heq.symm⟩, hd.ne'⟩, ?_, ?_⟩
    · simpa only [ite_eq_left heq, hdiv] using hz0
    · exact Prod.ext rfl hdiv
  · intro e he _
    have heq : e * (d / e) = d := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    exact (ite_eq_left heq).symm

end Ostmann

end OAI
