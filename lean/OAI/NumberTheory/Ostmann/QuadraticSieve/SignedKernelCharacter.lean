import OAI.NumberTheory.Ostmann.QuadraticSieve.PrimitiveKernelCharacter
import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedSquarefreeRange

namespace OAI

/-! # A primitive character for each non-small signed squarefree kernel -/

namespace Ostmann

private theorem prime_character_zero (χ : PrimitiveRealCharacter) {p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ χ.modulus) : χ.character p = 0 := by
  apply MulChar.map_nonunit
  intro hu
  have hc := (ZMod.isUnit_iff_coprime p χ.modulus).mp hu
  exact (hp.coprime_iff_not_dvd.mp hc) hdiv

private theorem prime_jacobi_zero (d : ℤ) {p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ d.natAbs) : jacobiSym d p = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  apply jacobiSym.eq_zero_iff_not_coprime.mpr
  rw [Int.gcd_eq_natAbs]
  intro hc
  have hc' : d.natAbs.Coprime p := by simpa only [Int.natAbs_natCast] using hc
  exact (hp.coprime_iff_not_dvd.mp hc'.symm) hdiv

/-- Equality at coprime odd arguments extends to all odd primes because
both characters vanish at a prime factor of the odd kernel. -/
theorem kernel_prime_character_value (d : ℤ) (N : ℕ) (χ : PrimitiveRealCharacter)
    (hNq : N ∣ χ.modulus) (hNd : N ∣ d.natAbs)
    (hvalue : ∀ a : ℕ, Odd a → a.Coprime N → χ.character a = (jacobiSym d a : ℝ)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  intro p hp hp2
  by_cases hdiv : p ∣ N
  · rw [prime_character_zero χ hp (hdiv.trans hNq),
      prime_jacobi_zero d hp (hdiv.trans hNd), Int.cast_zero]
  · exact hvalue p (hp.odd_of_ne_two hp2) (hp.coprime_iff_not_dvd.mpr hdiv)

/-- The auxiliary N is the odd part of the kernel. Its divisibility and
conductor bounds also give a finite list of possible kernels for a fixed
exceptional conductor. No character-classification result is assumed. -/
theorem exists_signed_kernel_character (d : ℤ) (hsf : Squarefree d.natAbs)
    (hd : 2 < d.natAbs) :
    ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
      1 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
      χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  have hmem : d ∈ signedSquarefreeRange d.natAbs := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, hd0, hsf⟩
    simpa only [Int.natCast_natAbs] using abs_le.mp (le_refl |d|)
  obtain ⟨c, hc, N, hNmem, heq⟩ := signedSquarefreeRange_cover hmem
  have hNsf : Squarefree N := (Finset.mem_filter.mp hNmem).2.2
  have hNodd : Odd N := (Finset.mem_filter.mp hNmem).2.1
  simp only [quadraticSigns, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · have hdN : d = (N : ℤ) := by simpa using heq.symm
    have habs : d.natAbs = N := by simp [hdN]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_odd_kernel_primitive N hN hNsf hNodd false
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, by omega, Or.inl habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [Bool.false_eq_true, ite_false, ← hdN] using hv
  · have hdN : d = -(N : ℤ) := by simpa using heq.symm
    have habs : d.natAbs = N := by simp [hdN]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_odd_kernel_primitive N hN hNsf hNodd true
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, by omega, Or.inl habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [ite_true, ← hdN] using hv
  · have hdN : d = 2 * (N : ℤ) := heq.symm
    have habs : d.natAbs = 2 * N := by simp [hdN, Int.natAbs_mul]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_even_kernel_primitive N hN hNsf hNodd false
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, hbound, Or.inr habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [Bool.false_eq_true, ite_false, ← hdN] using hv
  · have hdN : d = -(2 * (N : ℤ)) := by rw [← heq]; ring
    have habs : d.natAbs = 2 * N := by simp [hdN, Int.natAbs_mul]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_even_kernel_primitive N hN hNsf hNodd true
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, hbound, Or.inr habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [ite_true, ← hdN] using hv

end Ostmann

end OAI
