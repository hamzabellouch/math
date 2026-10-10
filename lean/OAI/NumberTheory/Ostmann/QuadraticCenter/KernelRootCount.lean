import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelDivisorBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelPopulation
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelRootArithmetic

namespace OAI

namespace Ostmann.QuadraticCenter

theorem unit_square_roots_card_le_two_divisors (S : Finset ℕ)
    {m : ℕ} (hm : 0 < m) (r : ℤ) (hr : IsCoprime r (m : ℤ))
    (hrange : ∀ t ∈ S, t < m)
    (hroot : ∀ t ∈ S, (m : ℤ) ∣ (t : ℤ) ^ 2 - r ^ 2) :
    S.card ≤ 2 * m.divisors.card := by
  classical
  let code : ℕ → ℕ × ℕ := fun t => (((t : ℤ) - r).gcd (m : ℤ), 2 * t / m)
  have hmap : ∀ t ∈ S, code t ∈ m.divisors ×ˢ Finset.range 2 := by
    intro t ht
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Nat.mem_divisors.mpr
        ⟨Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ((t : ℤ) - r) m), hm.ne'⟩
    · apply Finset.mem_range.mpr
      dsimp [code]
      apply (Nat.div_lt_iff_lt_mul hm).mpr
      exact Nat.mul_lt_mul_of_pos_left (hrange t ht) (by decide)
  have hinj : Set.InjOn code (↑S : Set ℕ) := by
    intro t ht s hs heq
    have hlabel := congrArg Prod.fst heq
    have hquot := congrArg Prod.snd heq
    dsimp [code] at hlabel hquot
    have hd := same_gcd_label_dvd_double_difference hm hr
      (hroot t ht) (hroot s hs) hlabel
    have hmod : Nat.ModEq m (2 * s) (2 * t) := Nat.modEq_iff_dvd.mpr (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_sub] using hd)
    have hsdiv := Nat.mod_add_div (2 * s) m
    have htdiv := Nat.mod_add_div (2 * t) m
    change (2 * s) % m = (2 * t) % m at hmod
    rw [hmod, ← hquot] at hsdiv
    omega
  have hb := Finset.card_le_card_of_injOn code hmap hinj
  simpa only [Finset.card_product, Finset.card_range, mul_comm] using hb

theorem kernel_root_coprime {m t : ℕ} {u h : ℤ}
    (hc : IsCoprime h (m : ℤ)) (ht : t ∈ kernelRootResidues m u h) :
    IsCoprime u (m : ℤ) ∧ IsCoprime (t : ℤ) (m : ℤ) := by
  have heq := (mem_kernelRootResidues.mp ht).2
  have hd : (m : ℤ) ∣ u * (t : ℤ) ^ 2 + h := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [heq]
    ring
  obtain ⟨k, hk⟩ := hd
  have hu : IsCoprime (u * (t : ℤ) ^ 2) (m : ℤ) := by
    have he : u * (t : ℤ) ^ 2 = (m : ℤ) * k - h := by linarith [hk]
    rw [he]
    simpa using hc
  refine ⟨hu.of_isCoprime_of_dvd_left (dvd_mul_right _ _), ?_⟩
  apply hu.of_isCoprime_of_dvd_left
  refine ⟨u * t, ?_⟩
  ring

theorem kernelRootResidues_card_le_four_sqrt {m : ℕ} (hm : 0 < m) {u h : ℤ}
    (hc : IsCoprime h (m : ℤ)) :
    (kernelRootResidues m u h).card ≤ 4 * Nat.sqrt m := by
  classical
  by_cases hne : (kernelRootResidues m u h).Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hcop := kernel_root_coprime hc hr
    have hb := unit_square_roots_card_le_two_divisors (kernelRootResidues m u h)
      hm (r : ℤ) hcop.2
      (fun t ht => (mem_kernelRootResidues.mp ht).1) ?_
    · exact hb.trans (by nlinarith [card_divisors_le_two_sqrt m])
    · intro t ht
      have hteq := (mem_kernelRootResidues.mp ht).2
      have hreq := (mem_kernelRootResidues.mp hr).2
      have hd : (m : ℤ) ∣ u * ((t : ℤ) ^ 2 - (r : ℤ) ^ 2) := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        push_cast
        rw [mul_sub, hteq, hreq]
        ring
      exact hcop.1.symm.dvd_of_dvd_mul_left hd
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end Ostmann.QuadraticCenter

end OAI
