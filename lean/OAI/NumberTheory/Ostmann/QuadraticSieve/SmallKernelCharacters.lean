import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedKernelCharacter

namespace OAI

/-! # The three nonprincipal kernels of absolute value at most two -/

namespace Ostmann

private theorem negative_one_kernel_ne_one : signedOddKernelCharacter 1 true ≠ 1 := by
  intro he
  have hv := signedOddKernelCharacter_value 1 true (by decide) 3 (by decide) (by decide)
  have hJ : jacobiSym (-1) 3 = -1 := by
    rw [jacobiSym.at_neg_one (by decide)]
    norm_num [ZMod.χ₄_nat_eq_if_mod_four]
  have hu : IsUnit ((3 : ℕ) : ZMod (Nat.lcm 1 4)) := (ZMod.isUnit_iff_coprime 3 _).mpr (by decide)
  rw [he, MulChar.one_apply hu] at hv
  norm_num [hJ] at hv

private theorem even_one_kernel_ne_one (negative : Bool) :
    signedEvenKernelCharacter 1 negative ≠ 1 := by
  intro he
  have hv := signedEvenKernelCharacter_value 1 negative (by decide) 5 (by decide) (by decide)
  have hu : IsUnit ((5 : ℕ) : ZMod (Nat.lcm 1 8)) := (ZMod.isUnit_iff_coprime 5 _).mpr (by decide)
  rw [he, MulChar.one_apply hu] at hv
  have hp : jacobiSym 2 5 = -1 := by
    rw [jacobiSym.at_two (by decide)]
    norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
  have hn : jacobiSym (-2) 5 = -1 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by rfl, jacobiSym.neg _ (by decide), hp]
    norm_num [ZMod.χ₄_nat_eq_if_mod_four]
  cases negative <;> norm_num [hp, hn] at hv

/-- The small characters are constructed from the same twists and checked at
3 or 5. Their conductors are bounded by the original levels 4 and 8. -/
theorem exists_negative_one_kernel_character :
    ∃ χ : PrimitiveRealCharacter, χ.modulus ≤ 4 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym (-1) p : ℝ) := by
  let : NeZero (Nat.lcm 1 4) := ⟨by simp⟩
  let ψ := signedOddKernelCharacter 1 true
  let χ := primitiveRealOfCharacter ψ negative_one_kernel_ne_one
  have hbound : χ.modulus ≤ 4 := by
    change (signedOddKernelCharacter 1 true).conductor ≤ 4
    simpa using (signedOddKernelCharacter_conductor_bounds 1 true (by simp) (by decide)).2
  refine ⟨χ, hbound, ?_⟩
  intro p hp hp2
  have hpodd := hp.odd_of_ne_two hp2
  have hcop : p.Coprime (Nat.lcm 1 4) := by
    simpa using hpodd.coprime_two_right.pow_right 2
  dsimp only [χ]
  rw [primitiveRealOfCharacter_value ψ negative_one_kernel_ne_one p hcop]
  simpa using signedOddKernelCharacter_value 1 true (by decide) p hcop hpodd

theorem exists_even_one_kernel_character (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, χ.modulus ≤ 8 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        χ.character p = (jacobiSym (if negative then -2 else 2) p : ℝ) := by
  let : NeZero (Nat.lcm 1 8) := ⟨by simp⟩
  let ψ := signedEvenKernelCharacter 1 negative
  let χ := primitiveRealOfCharacter ψ (even_one_kernel_ne_one negative)
  have hbound : χ.modulus ≤ 8 := by
    change (signedEvenKernelCharacter 1 negative).conductor ≤ 8
    simpa using (signedEvenKernelCharacter_conductor_bounds 1 negative (by simp) (by decide)).2
  refine ⟨χ, hbound, ?_⟩
  intro p hp hp2
  have hpodd := hp.odd_of_ne_two hp2
  have hcop : p.Coprime (Nat.lcm 1 8) := by
    simpa using hpodd.coprime_two_right.pow_right 3
  dsimp only [χ]
  rw [primitiveRealOfCharacter_value ψ (even_one_kernel_ne_one negative) p hcop]
  simpa using signedEvenKernelCharacter_value 1 negative (by decide) p hcop hpodd

/-- Every nonprincipal nonzero squarefree kernel has the same conductor
and odd-prime properties, including the three small cases. -/
theorem exists_nonprincipal_kernel_character (d : ℤ)
    (hsf : Squarefree d.natAbs) (hzero : d ≠ 0) (hone : d ≠ 1) :
    ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
      0 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
      χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  by_cases hd : 2 < d.natAbs
  · obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, hv⟩ := exists_signed_kernel_character d hsf hd
    exact ⟨χ, N, by omega, hNq, hqN, hdN, hqd, hdq, hv⟩
  · have habs : |d| ≤ 2 := by
      have hh : (d.natAbs : ℤ) ≤ 2 := by exact_mod_cast (le_of_not_gt hd)
      simpa only [Int.natCast_natAbs] using hh
    have hlo := (abs_le.mp habs).1
    have hhi := (abs_le.mp habs).2
    interval_cases d
    · obtain ⟨χ, hq, hv⟩ := exists_even_one_kernel_character true
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by simpa using hq, ?_, ?_, ?_, ?_⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
      · simpa using hv
    · obtain ⟨χ, hq, hv⟩ := exists_negative_one_kernel_character
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by omega, ?_, ?_, ?_, hv⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
    · exact (hzero rfl).elim
    · exact (hone rfl).elim
    · obtain ⟨χ, hq, hv⟩ := exists_even_one_kernel_character false
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by simpa using hq, ?_, ?_, ?_, ?_⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
      · simpa using hv

end Ostmann

end OAI
