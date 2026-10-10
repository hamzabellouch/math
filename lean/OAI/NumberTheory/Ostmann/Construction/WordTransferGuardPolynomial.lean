import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardReplay

namespace OAI

/-! # The exact one-variable polynomial form of each branching node guard -/

namespace Ostmann

open scoped Classical

noncomputable def WordTransferGuard.residueAt {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.pivot.cleared.numerator)
    g.pivot.cleared.denominator g.right.natAbs ∧
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.rightProduct.cleared.numerator)
    g.rightProduct.cleared.denominator g.root.natAbs

def WordTransferGuard.frequencyBounds {σ : Type*} (g : WordTransferGuard σ) : Prop :=
  g.left.natAbs ≤ g.childBound ∧ g.right.natAbs ≤ g.childBound

noncomputable def WordTransferGuard.polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) : Fin 3 → Polynomial ℝ :=
  ![formulaPolynomial g.pivot (fun j => (a j : ℝ)) coord - Polynomial.C 1,
    Polynomial.C (g.pivotBound : ℝ) - formulaPolynomial g.pivot (fun j => (a j : ℝ)) coord,
    formulaPolynomial g.rightProduct (fun j => (a j : ℝ)) coord -
      Polynomial.C ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ)]

theorem WordTransferGuard.gap_iff {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ)
    (h : g.residueAt x) :
    ((2 * g.pivotBound * g.childBound : ℕ) : ℝ) < g.rightProduct.realValue x ↔
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realValue x := by
  obtain ⟨y, hy, _⟩ := (g.rightProduct.smallDivisionTest_iff x g.root.natAbs).mp h.2
  have he : g.rightProduct.realValue x = (y : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hy, Rat.cast_intCast]
  rw [he]
  constructor
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by omega
    exact_mod_cast hj
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by omega
    exact_mod_cast hj

/-- Strict product gaps are closed polynomial inequalities because the
residue tests already enforce the exact integral word values. -/
theorem WordTransferGuard.validAt_polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    g.ValidAt (Function.update a coord z) ↔
      g.residueAt (Function.update a coord z) ∧ g.frequencyBounds ∧
        ∀ j, 0 ≤ (g.polynomials a coord j).eval (z : ℝ) := by
  have hrange : (∀ j, 0 ≤ (g.polynomials a coord j).eval (z : ℝ)) ↔
      1 ≤ g.pivot.realValue (Function.update a coord z) ∧
      g.pivot.realValue (Function.update a coord z) ≤ g.pivotBound ∧
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤
        g.rightProduct.realValue (Function.update a coord z) := by
    simp only [polynomials, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Fin.forall_fin_zero, Polynomial.eval_sub, Polynomial.eval_C,
      formulaPolynomial_eval_update, sub_nonneg, and_true]
  rw [hrange]
  constructor
  · rintro ⟨hp, hr, hlo, hhi, hgap, hv, hw⟩
    exact ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, (g.gap_iff _ ⟨hp, hr⟩).mp hgap⟩
  · rintro ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, hgap⟩
    exact ⟨hp, hr, hlo, hhi, (g.gap_iff _ ⟨hp, hr⟩).mpr hgap, hv, hw⟩

/-- Each node contributes three inequalities of derived polynomial degree. -/
theorem WordTransferGuard.polynomials_degree {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) :
    ∀ j, (g.polynomials a coord j).natDegree ≤ max g.pivot.cost g.rightProduct.cost := by
  intro j
  fin_cases j
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, zero_max]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_left _ _)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (formulaPolynomial_degree _ _ _).trans (Nat.le_max_right _ _)

end Ostmann

end OAI
