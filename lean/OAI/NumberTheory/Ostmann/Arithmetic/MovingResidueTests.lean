import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticSupport

namespace OAI

/-! # Three explicit residue tests at each original moving node -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingFormulaNode.testFormulas (f : MovingFormulaNode) : Fin 3 → HistoryFormula Bool :=
  ![f.guard.pivot, f.guard.rightProduct, f.newGiant]

def MovingFormulaNode.testModuli (f : MovingFormulaNode) : Fin 3 → ℕ :=
  ![f.guard.right.natAbs, f.guard.root.natAbs, 1]

noncomputable def MovingFormulaNode.residueTests (f : MovingFormulaNode) (a : Bool → ℤ) : Prop :=
  ∀ j, smallDivisionTest
    (MvPolynomial.eval₂Hom (RingHom.id ℤ) a (f.testFormulas j).cleared.numerator)
    (f.testFormulas j).cleared.denominator (f.testModuli j)

theorem formula_integral_small_test (F : HistoryFormula Bool) (a : Bool → ℤ) :
    F.IntegralAt a ↔ smallDivisionTest
      (MvPolynomial.eval₂Hom (RingHom.id ℤ) a F.cleared.numerator) F.cleared.denominator 1 := by
  rw [F.integralAt_iff]
  have hu (z : ℤ) : IsUnit (z : ZMod 1) := by
    rw [Subsingleton.elim (z : ZMod 1) 1]
    exact isUnit_one
  simp only [smallDivisionTest, hu, and_true]

theorem MovingFormulaNode.residueTests_iff (f : MovingFormulaNode) (a : Bool → ℤ) :
    f.residueTests a ↔ f.guard.residueAt a ∧ f.newGiant.IntegralAt a := by
  simp only [residueTests, testFormulas, testModuli, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Fin.forall_fin_zero, and_true, WordTransferGuard.residueAt, ← formula_integral_small_test,
    and_assoc]

/-- The actual common period is built from the cleared formula denominators
and the two retained frequency moduli. -/
noncomputable def MovingFormulaNode.residuePeriod (f : MovingFormulaNode) : ℕ :=
  ∏ j : Fin 3, (f.testFormulas j).cleared.denominator.natAbs * f.testModuli j

theorem MovingFormulaNode.residuePeriod_pos (f : MovingFormulaNode)
    (hw : f.guard.right ≠ 0) (hs : f.guard.root ≠ 0) : 0 < f.residuePeriod := by
  apply Finset.prod_pos
  intro j _
  apply Nat.mul_pos (Int.natAbs_pos.mpr (f.testFormulas j).cleared.denominator_ne_zero)
  fin_cases j
  · exact Int.natAbs_pos.mpr hw
  · exact Int.natAbs_pos.mpr hs
  · exact Nat.zero_lt_one

theorem MovingFormulaNode.test_period_dvd (f : MovingFormulaNode) (j : Fin 3) :
    (f.testFormulas j).cleared.denominator * (f.testModuli j : ℤ) ∣ (f.residuePeriod : ℤ) := by
  apply Int.dvd_natCast.mpr
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact Finset.dvd_prod_of_mem (fun j : Fin 3 =>
    (f.testFormulas j).cleared.denominator.natAbs * f.testModuli j) (Finset.mem_univ j)

/-- All three tests are constant on the constructed residue classes. -/
theorem MovingFormulaNode.residueTests_modEq (f : MovingFormulaNode)
    (a b : Bool → ℤ) (h : ∀ i, a i ≡ b i [ZMOD f.residuePeriod]) :
    f.residueTests a ↔ f.residueTests b := by
  apply forall_congr'
  intro j
  exact cleared_history_test_residue_invariant (f.testFormulas j).cleared.numerator
    a b f.residuePeriod (f.testFormulas j).cleared.denominator (f.testModuli j)
    (f.testFormulas j).cleared.denominator_ne_zero (f.test_period_dvd j) h

noncomputable def movingGiantUpdate (a : Bool → ℤ) (coord : Bool) (z : ℤ) : Bool → ℤ :=
  @Function.update Bool (fun _ => ℤ) (fun x y => Classical.propDecidable (x = y)) a coord z

/-- At a fixed residue class, the remaining arithmetic support uses only
three explicit polynomial inequalities and fixed frequency bounds. -/
theorem MovingFormulaNode.holds_polynomials (f : MovingFormulaNode)
    (a : Bool → ℤ) (coord : Bool) (z : ℤ) :
    (f.guard.ValidAt (movingGiantUpdate a coord z) ∧ f.newGiant.IntegralAt (movingGiantUpdate a coord z)) ↔
      f.residueTests (movingGiantUpdate a coord z) ∧ f.guard.frequencyBounds ∧
        ∀ j, 0 ≤ (f.guard.polynomials a coord j).eval (z : ℝ) := by
  rw [residueTests_iff]
  have hg := f.guard.validAt_polynomials a coord z
  change (f.guard.ValidAt _ ∧ _) ↔ _
  rw [show f.guard.ValidAt (movingGiantUpdate a coord z) ↔
    f.guard.residueAt (movingGiantUpdate a coord z) ∧ f.guard.frequencyBounds ∧
      ∀ j, 0 ≤ (f.guard.polynomials a coord j).eval (z : ℝ) from hg]
  tauto

end Ostmann

end OAI
