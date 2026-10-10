import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Construction

private theorem exists_mem_mod_three_eq_two_of_prod
    (L : List ℕ) (hL : L.prod % 3 = 2) :
    ∃ p ∈ L, p % 3 = 2 := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
      by_cases ha : a % 3 = 2
      · exact ⟨a, List.mem_cons_self, ha⟩
      · have hmod : a % 3 = 0 ∨ a % 3 = 1 := by
          have := Nat.mod_lt a (by decide : 0 < 3)
          omega
        rcases hmod with ha0 | ha1
        · simp only [List.prod_cons, Nat.mul_mod, ha0, zero_mul, Nat.zero_mod] at hL
          contradiction
        · have htail : L.prod % 3 = 2 := by
            simpa only [List.prod_cons, Nat.mul_mod, ha1, one_mul, Nat.mod_mod] using hL
          obtain ⟨p, hp, hpmod⟩ := ih htail
          exact ⟨p, List.mem_cons_of_mem a hp, hpmod⟩

theorem exists_prime_dvd_mod_three_eq_two {n : ℕ} (hn : n % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 3 = 2 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hp, hpmod⟩ :=
    exists_mem_mod_three_eq_two_of_prod n.primeFactorsList
      (by simpa only [Nat.prod_primeFactorsList hn0] using hn)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp,
    Nat.dvd_of_mem_primeFactorsList hp, hpmod⟩

theorem exists_prime_gt_mod_three_eq_two (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ p % 3 = 2 := by
  let N := 3 * B.factorial - 1
  have hfacpos := Nat.factorial_pos B
  have hsucc : N + 1 = 3 * B.factorial := by
    dsimp [N]
    exact Nat.sub_add_cancel (by omega)
  have hNmod : N % 3 = 2 := by omega
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_dvd_mod_three_eq_two hNmod
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hnot
  have hpB : p ≤ B := Nat.le_of_not_gt hnot
  have hpfac : p ∣ B.factorial := Nat.dvd_factorial hp.pos hpB
  have hpprod : p ∣ 3 * B.factorial := dvd_mul_of_dvd_right hpfac 3
  have hsub : 3 * B.factorial - N = 1 := by omega
  have hpone : p ∣ 1 := by
    have h := Nat.dvd_sub hpprod hpN
    simpa only [hsub] using h
  have hple := Nat.le_of_dvd (by decide : 0 < 1) hpone
  have hptwo := hp.two_le
  omega

end RyserCoveringCounterexample.Construction

end OAI
