import OAI.Probability.ThorpShuffle.MixingBounds

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Parity
open Conditional

def sign (d : ℕ) (g : State d) : ℝ := ((Equiv.Perm.sign g : ℤˣ) : ℤ)

theorem sign_mul (d : ℕ) (g h : State d) : sign d (g * h) = sign d g * sign d h := by
  simp [sign]

theorem step_toggle (d : ℕ) (s : Position d) (c : Coins (d + 1)) :
    step (d + 1) (toggleCoin s c) =
      step (d + 1) c * Equiv.swap (Fin.cons false s) (Fin.cons true s) := by
  classical
  change Position d → Bool at c
  apply Equiv.Perm.ext
  intro x
  obtain ⟨⟨b, t⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change (rotate (d + 1)) (Fin.cons (b ^^ toggleCoin s c t) t) =
    step (d + 1) c (Equiv.swap (Fin.cons false s) (Fin.cons true s) (Fin.cons b t))
  by_cases ht : t = s
  · subst t
    cases b <;> simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · change rotate (d + 1) (Fin.cons (false ^^ toggleCoin s c s) s) =
        rotate (d + 1) (Fin.cons (true ^^ c s) s)
      have hh : toggleCoin s c s = !(c s) := by
        change Function.update c s (!(c s)) s = !(c s)
        simp
      rw [hh]
      simp
    · change rotate (d + 1) (Fin.cons (true ^^ toggleCoin s c s) s) =
        rotate (d + 1) (Fin.cons (false ^^ c s) s)
      have hh : toggleCoin s c s = !(c s) := by
        change Function.update c s (!(c s)) s = !(c s)
        simp
      rw [hh]
      simp
  · have hf : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons false s := by
      intro he; apply ht; simpa using congrArg Fin.tail he
    have htr : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons true s := by
      intro he; apply ht; simpa using congrArg Fin.tail he
    rw [Equiv.swap_apply_of_ne_of_ne hf htr]
    change rotate (d + 1) (Fin.cons (b ^^ toggleCoin s c t) t) =
      rotate (d + 1) (Fin.cons (b ^^ c t) t)
    have hh : toggleCoin s c t = c t := by
      change Function.update c s (!(c s)) t = c t
      exact Function.update_of_ne ht _ _
    rw [hh]

theorem sign_step_toggle (d : ℕ) (s : Position d) (c : Coins (d + 1)) :
    sign (d + 1) (step (d + 1) (toggleCoin s c)) =
      -sign (d + 1) (step (d + 1) c) := by
  classical
  rw [step_toggle, sign_mul]
  have hne : (Fin.cons false s : Position (d + 1)) ≠ Fin.cons true s := by
    intro he
    have hh := congrFun he 0
    simp at hh
  simp [sign, Equiv.Perm.sign_swap hne]

theorem mean_sign_step (d : ℕ) :
    mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) = 0 := by
  classical
  let s : Position d := fun _ => false
  have hh := mean_equiv (toggleCoin s)
    (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c))
  change mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) (toggleCoin s c))) =
    mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) at hh
  simp_rw [sign_step_toggle] at hh
  have hn : mean (fun c : Coins (d + 1) => -sign (d + 1) (step (d + 1) c)) =
      -mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) := by
    simp only [mean, Finset.sum_neg_distrib, neg_div]
  rw [hn] at hh
  linarith

theorem mean_sign_run (d t : ℕ) :
    mean (fun ω : History (d + 1) (t + 1) => sign (d + 1) (run (d + 1) (t + 1) ω)) = 0 := by
  rw [mean_history_succ]
  simp only [run_snoc, sign_mul, mean_mul_const, mean_sign_step, zero_mul, mean_zero]

theorem law_sign_zero (d t : ℕ) :
    (∑ g : State (d + 1), law (d + 1) (t + 1) g * sign (d + 1) g) = 0 := by
  rw [law, fairMass_test]
  exact mean_sign_run d t

end Parity

end Thorp

end

end OAI
