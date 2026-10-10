import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteParameterChain

namespace OAI

/-! # The exact density product along a finite controlled collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def controlledPath (next : ℕ → State → StageControls → State) (controls : ℕ → StageControls)
    (i : ℕ) (z : State) : ℕ → State
  | 0 => z
  | n+1 => next (i+n) (controlledPath next controls i z n) (controls (i+n))

theorem controlledPath_shift (next : ℕ → State → StageControls → State)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    controlledPath next controls i z (n+1) =
      controlledPath next controls (i+1) (next i z (controls i)) n := by
  induction n with
  | zero => simp only [controlledPath,Nat.add_zero]
  | succ n ih =>
    change next (i+(n+1)) (controlledPath next controls i z (n+1)) (controls (i+(n+1))) =
      next ((i+1)+n) (controlledPath next controls (i+1) (next i z (controls i)) n)
        (controls ((i+1)+n))
    have he : i+(n+1) = (i+1)+n := by omega
    rw [ih,he]

theorem controlledPath_zero (next : ℕ → State → StageControls → State)
    (controls : ℕ → StageControls) (i : ℕ) (z : State) :
    controlledPath next controls i z 0 = z := rfl

theorem chainIntegrand_eq_pathProduct (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    chainIntegrand next density g i n z (fun j => controls (i+j.val)) =
      (∏ j : Fin n, density (i+j.val) (controlledPath next controls i z j.val)
        (controls (i+j.val))) * g (controlledPath next controls i z n) := by
  induction n generalizing i z with
  | zero => simp only [chainIntegrand,controlledPath,Fin.prod_univ_zero,one_mul]
  | succ n ih =>
    rw [chainIntegrand]
    have htail : Fin.tail (fun j : Fin (n+1) => controls (i+j.val)) =
        (fun j : Fin n => controls ((i+1)+j.val)) := by
      funext j
      change controls (i+(j.val+1)) = controls ((i+1)+j.val)
      congr 1
      omega
    rw [htail,ih]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,controlledPath_shift,controlledPath_zero]
    have he (j : Fin n) : i+(j.val+1) = (i+1)+j.val := by omega
    simp only [he,mul_assoc]

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
