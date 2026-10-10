import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter

theorem card_divisors_le_two_sqrt (m : ℕ) :
    m.divisors.card ≤ 2 * Nat.sqrt m := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let code : ℕ → Bool × ℕ := fun d =>
    if d ≤ Nat.sqrt m then (false, d) else (true, m / d)
  have hcode : ∀ d ∈ m.divisors, code d ∈ (Finset.univ : Finset Bool) ×ˢ
      Finset.Icc 1 (Nat.sqrt m) := by
    intro d hd
    have hdm := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hmpos
    have hprod : d * (m / d) = m := Nat.mul_div_cancel' hdm
    have hqpos : 0 < m / d := by nlinarith
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [code]
    split_ifs with hs
    · exact Finset.mem_Icc.mpr ⟨hdpos, hs⟩
    · apply Finset.mem_Icc.mpr
      refine ⟨hqpos, ?_⟩
      by_contra hq
      have hb := Nat.lt_succ_sqrt m
      have hdlo : Nat.sqrt m + 1 ≤ d := by omega
      have hqlo : Nat.sqrt m + 1 ≤ m / d := by omega
      have := Nat.mul_le_mul hdlo hqlo
      nlinarith
  have hinj : Set.InjOn code (↑m.divisors : Set ℕ) := by
    intro a ha b hb hc
    have ham := (Nat.mem_divisors.mp ha).1
    have hbm := (Nat.mem_divisors.mp hb).1
    have haprod : a * (m / a) = m := Nat.mul_div_cancel' ham
    have hbprod : b * (m / b) = m := Nat.mul_div_cancel' hbm
    have hap : 0 < m / a := by nlinarith
    dsimp [code] at hc
    split_ifs at hc with ha' hb' hb'
    · exact congrArg Prod.snd hc
    · cases congrArg Prod.fst hc
    · cases congrArg Prod.fst hc
    · have hq := congrArg Prod.snd hc
      dsimp at hq
      rw [← hq] at hbprod
      exact Nat.eq_of_mul_eq_mul_right hap (haprod.trans hbprod.symm)
  have hc := Finset.card_le_card_of_injOn code hcode hinj
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.card_Icc,
    Nat.add_sub_cancel] using hc

end Ostmann.QuadraticCenter

end OAI
