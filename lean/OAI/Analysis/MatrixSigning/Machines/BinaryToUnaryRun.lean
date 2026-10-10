import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.UnaryArithmetic
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryMachine

namespace OAI

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W03.UnaryArithmetic KS.W19

theorem run_budget_append (a b c : Config 3 8) (t u : ℕ)
    (hab : ∀ coins, coins.length = t → machine.run a coins = b)
    (hbc : ∀ coins, coins.length = u → machine.run b coins = c)
    (coins : List Bool) (hlen : coins.length = t + u) : machine.run a coins = c := by
  have ht : (coins.take t).length = t := by simp only [List.length_take, hlen]; omega
  have hu : (coins.drop t).length = u := by simp only [List.length_drop, hlen]; omega
  conv_lhs => rw [← List.take_append_drop t coins]
  erw [Machine.run_append, hab _ ht, hbc _ hu]

theorem run_reverse (xs ys zs coins : List Bool) (hlen : coins.length = xs.length) :
    machine.run (cfg (some 0) xs ys zs) coins =
      cfg (some 0) [] ys (xs.reverse ++ zs) := by
  induction xs generalizing zs coins with
  | nil =>
    have hc : coins = [] := List.length_eq_zero_iff.mp hlen
    subst coins
    rfl
  | cons b bs ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      erw [Machine.run.eq_2, reverse_step, ih _ _ (by simpa using hlen)]
      simp [List.reverse_cons, List.append_assoc]
      rfl

theorem run_double (b : Bool) (n k : ℕ) (unread coins : List Bool)
    (hlen : coins.length = 2 * n) :
    machine.run (cfg (some (doubleState b)) (List.replicate k true)
      (List.replicate n true) unread) coins =
      cfg (some (doubleState b)) (List.replicate (2 * n + k) true) [] unread := by
  induction n generalizing k coins with
  | zero =>
    have hc : coins = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst coins
    simp [Machine.run]
    rfl
  | succ n ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      cases cs with
      | nil => simp at hlen; omega
      | cons d ds =>
        erw [List.replicate_succ, Machine.run.eq_2, double_step, Machine.run.eq_2, second_step]
        change machine.run (cfg (some (doubleState b)) (List.replicate (k + 2) true)
          (List.replicate n true) unread) ds = _
        rw [ih (k + 2) ds (by simp only [List.length_cons] at hlen; omega)]
        congr 2
        omega

theorem run_restore (b : Bool) (n k : ℕ) (unread coins : List Bool)
    (hlen : coins.length = n) :
    machine.run (cfg (some (restoreState b)) (List.replicate n true)
      (List.replicate k true) unread) coins =
      cfg (some (restoreState b)) [] (List.replicate (n + k) true) unread := by
  induction n generalizing k coins with
  | zero =>
    have hc : coins = [] := List.length_eq_zero_iff.mp hlen
    subst coins
    simp [Machine.run]
    rfl
  | succ n ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      erw [List.replicate_succ, Machine.run.eq_2, restore_step]
      change machine.run (cfg (some (restoreState b)) (List.replicate n true)
        (List.replicate (k + 1) true) unread) cs = _
      rw [ih (k + 1) cs (by simpa using hlen)]
      congr 2
      omega

theorem run_round (b : Bool) (n : ℕ) (unread coins : List Bool)
    (hlen : coins.length = 4 * n + 2) :
    machine.run (cfg (some (doubleState b)) [] (List.replicate n true) unread) coins =
      cfg (some 1) [] (List.replicate (2 * n + digit b) true) unread := by
  apply run_budget_append _
    (cfg (some (doubleState b)) (List.replicate (2 * n) true) [] unread) _
    (2 * n) (2 * n + 2) ?_ ?_ coins (by omega)
  · intro cs hcs
    simpa using run_double b n 0 unread cs hcs
  · intro cs hcs
    cases cs with
    | nil => simp at hcs
    | cons c rest =>
      erw [Machine.run.eq_2, double_done]
      apply run_budget_append _
        (cfg (some (restoreState b)) [] (List.replicate (2 * n) true) unread) _
        (2 * n) 1 ?_ ?_ rest (by
        simp only [List.length_cons] at hcs; omega)
      · intro ds hds
        simpa using run_restore b (2 * n) 0 unread ds hds
      · intro ds hds
        cases ds with
        | nil => simp at hds
        | cons d tail =>
          have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hds)
          subst tail
          erw [Machine.run.eq_2, restore_done]
          cases b <;> simp [Machine.run, digit, List.replicate_succ] <;> rfl

theorem run_loop (xs : List Bool) (n : ℕ) (coins : List Bool)
    (hlen : coins.length = ticks xs n) :
    machine.run (cfg (some 1) [] (List.replicate n true) xs) coins =
      cfg none [] (List.replicate (accumulate xs n) true) [] := by
  induction xs generalizing n coins with
  | nil =>
    cases coins with
    | nil => simp [ticks] at hlen
    | cons c cs =>
      have ht : cs = [] := List.length_eq_zero_iff.mp (by simpa [ticks] using hlen)
      subst cs
      erw [Machine.run.eq_2, guard_done]
      rfl
  | cons b bs ih =>
    cases coins with
    | nil => simp [ticks] at hlen; omega
    | cons c cs =>
      erw [Machine.run.eq_2, guard_step]
      apply run_budget_append _
        (cfg (some 1) [] (List.replicate (2 * n + digit b) true) bs) _
        (4 * n + 2) (ticks bs (2 * n + digit b))
        (run_round b n bs) (ih (2 * n + digit b)) cs
      simp only [List.length_cons, ticks] at hlen
      omega

theorem run_input_exact (xs coins : List Bool) (hlen : coins.length = totalTicks xs) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] := by
  rw [init_eq]
  apply run_budget_append _ (cfg (some 0) [] [] xs.reverse) _
    xs.length (1 + ticks xs.reverse 0) ?_ ?_ coins (by
    unfold totalTicks at hlen; omega)
  · intro cs hcs
    simpa using run_reverse xs [] [] cs hcs
  · intro cs hcs
    cases cs with
    | nil => simp at hcs; omega
    | cons c rest =>
      erw [Machine.run.eq_2, reverse_done]
      have hr := run_loop xs.reverse 0 rest (by simp only [List.length_cons] at hcs; omega)
      simpa only [accumulate_reverse, List.replicate_zero] using hr

end KS.W03.BinaryToUnary

end OAI
