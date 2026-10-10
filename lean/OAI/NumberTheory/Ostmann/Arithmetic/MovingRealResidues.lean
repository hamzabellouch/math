import OAI.NumberTheory.Ostmann.Arithmetic.MovingTopCells

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

noncomputable def HistoryFormula.realEval {σ : Type*} (F : HistoryFormula σ) (x : σ → ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) x F.cleared.numerator / F.cleared.denominator

noncomputable def WordTransferGuard.archimedeanAt {σ : Type*}
    (g : WordTransferGuard σ) (x : σ → ℝ) : Prop :=
  1 ≤ g.pivot.realEval x ∧ g.pivot.realEval x ≤ g.pivotBound ∧
    ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realEval x

/-- Integrality turns the strict integer gap into the closed real inequality.
All divisibility and unit tests remain in the residue factor. -/
theorem WordTransferGuard.validAt_residue_archimedean {σ : Type*}
    (g : WordTransferGuard σ) (x : σ → ℤ) :
    g.ValidAt x ↔ g.residueAt x ∧ g.frequencyBounds ∧
      g.archimedeanAt (fun i => (x i : ℝ)) := by
  change g.ValidAt x ↔ g.residueAt x ∧ g.frequencyBounds ∧
    (1 ≤ g.pivot.realValue x ∧ g.pivot.realValue x ≤ g.pivotBound ∧
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realValue x)
  constructor
  · rintro ⟨hp, hr, hlo, hhi, hgap, hv, hw⟩
    exact ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, (g.gap_iff x ⟨hp, hr⟩).mp hgap⟩
  · rintro ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, hgap⟩
    exact ⟨hp, hr, hlo, hhi, (g.gap_iff x ⟨hp, hr⟩).mpr hgap, hv, hw⟩

theorem MovingFormulaNode.holds_residue_archimedean (f : MovingFormulaNode) (a : Bool → ℤ) :
    (f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔
      f.residueTests a ∧ f.guard.frequencyBounds ∧
        f.guard.archimedeanAt (fun i => (a i : ℝ)) := by
  rw [f.guard.validAt_residue_archimedean, f.residueTests_iff]
  tauto

noncomputable def movingResidueGate (nodes : List MovingFormulaNode) (a : Bool → ℤ) : Prop :=
  ∀ f ∈ nodes, f.residueTests a ∧ f.guard.frequencyBounds

noncomputable def movingArchimedeanGate (nodes : List MovingFormulaNode) (x : Bool → ℝ) : Prop :=
  ∀ f ∈ nodes, f.guard.archimedeanAt x

/-- The real factor is evaluated at the actual point, while the residue
factor may use any representative of the constructed common period. -/
theorem movingFormulaNodes_residue_real (nodes : List MovingFormulaNode)
    (x a : Bool → ℤ) (hres : ∀ i, x i ≡ a i [ZMOD movingArithmeticPeriod nodes]) :
    (∀ f ∈ nodes, f.guard.ValidAt x ∧ f.newGiant.IntegralAt x) ↔
      movingResidueGate nodes a ∧ movingArchimedeanGate nodes (fun i => (x i : ℝ)) := by
  have hfres (f : MovingFormulaNode) (hf : f ∈ nodes) : f.residueTests x ↔ f.residueTests a :=
    f.residueTests_modEq x a (fun i => (hres i).of_dvd
      (by exact_mod_cast movingArithmeticPeriod_dvd nodes f hf))
  constructor
  · intro h
    constructor
    · intro f hf
      have hx := (f.holds_residue_archimedean x).mp (h f hf)
      exact ⟨(hfres f hf).mp hx.1, hx.2.1⟩
    · intro f hf
      exact ((f.holds_residue_archimedean x).mp (h f hf)).2.2
  · rintro ⟨hr, ha⟩ f hf
    exact (f.holds_residue_archimedean x).mpr
      ⟨(hfres f hf).mpr (hr f hf).1, (hr f hf).2, ha f hf⟩

def topGiantReal (XL XR : ℝ) (b : Bool) : ℝ := if b then XR else XL

noncomputable def WordTransferGuard.realPolynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) : Fin 3 → Polynomial ℝ :=
  ![formulaPolynomial g.pivot a coord - Polynomial.C 1,
    Polynomial.C (g.pivotBound : ℝ) - formulaPolynomial g.pivot a coord,
    formulaPolynomial g.rightProduct a coord -
      Polynomial.C ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ)]

theorem WordTransferGuard.archimedeanAt_polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) (z : ℝ) :
    g.archimedeanAt (Function.update a coord z) ↔
      ∀ j, 0 ≤ (g.realPolynomials a coord j).eval z := by
  simp only [archimedeanAt, realPolynomials, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.forall_fin_zero,
    Polynomial.eval_sub, Polynomial.eval_C, formulaPolynomial, normalizedHistoryPolynomial_eval,
    HistoryFormula.realEval, sub_nonneg, and_true]

theorem WordTransferGuard.realPolynomials_degree {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) (j : Fin 3) :
    (g.realPolynomials a coord j).natDegree ≤ max g.pivot.cost g.rightProduct.cost := by
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

noncomputable def movingArchimedeanRootCuts (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) : Finset ℝ :=
  nodes.toFinset.biUnion fun f => polynomialRootCuts (f.guard.realPolynomials a coord)

noncomputable def movingRealUpdate (a : Bool → ℝ) (coord : Bool) (z : ℝ) : Bool → ℝ :=
  @Function.update Bool (fun _ => ℝ) (fun x y => Classical.propDecidable (x = y)) a coord z

theorem movingArchimedeanRootCuts_mem (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) (f : MovingFormulaNode) (hf : f ∈ nodes)
    (j : Fin 3) (r : ℝ) (hr : r ∈ (f.guard.realPolynomials a coord j).roots) :
    r ∈ movingArchimedeanRootCuts nodes a coord := by
  exact Finset.mem_biUnion.mpr ⟨f, List.mem_toFinset.mpr hf,
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩⟩

theorem movingArchimedeanGate_rootCell (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) (S : Finset ℝ)
    (hS : movingArchimedeanRootCuts nodes a coord ⊆ S) (x y : ℝ)
    (hcode : rootCellCode S x = rootCellCode S y) :
    movingArchimedeanGate nodes (movingRealUpdate a coord x) ↔
      movingArchimedeanGate nodes (movingRealUpdate a coord y) := by
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  dsimp only [movingRealUpdate]
  rw [f.guard.archimedeanAt_polynomials a coord x, f.guard.archimedeanAt_polynomials a coord y]
  apply forall_congr'
  intro j
  exact polynomial_nonneg_iff_of_root_cell _ S
    (fun r hr => hS (movingArchimedeanRootCuts_mem nodes a coord f hf j r hr)) hcode

theorem movingArithmeticSupport_residue_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    T.ArithmeticSupport value childBound pivotBound XL XR ↔
      movingResidueGate nodes (topGiantInput a b) ∧ movingArchimedeanGate nodes (topGiantReal XL XR) := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  have hform := T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR
    (.prime false) (.prime true) (topGiantInput XL XR) (by simp [topGiantInput]) (by simp [topGiantInput])
  rw [← hform]
  have hres : ∀ i, topGiantInput XL XR i ≡ topGiantInput a b i [ZMOD movingArithmeticPeriod nodes] := by
    intro i
    cases i
    · exact hL.of_dvd (by exact_mod_cast hM)
    · exact hR.of_dvd (by exact_mod_cast hM)
  have h := movingFormulaNodes_residue_real nodes (topGiantInput XL XR) (topGiantInput a b) hres
  have he : (fun i => (topGiantInput XL XR i : ℝ)) = topGiantReal XL XR := by
    funext i
    cases i <;> rfl
  simpa only [he] using h

end Ostmann

end OAI
