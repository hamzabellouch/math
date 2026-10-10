import OAI.NumberTheory.Ostmann.Arithmetic.MovingResidueTests

namespace OAI

/-! # Constructed residue and root cells for full moving arithmetic support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingArithmeticPeriod (nodes : List MovingFormulaNode) : ℕ :=
  (nodes.map MovingFormulaNode.residuePeriod).prod

noncomputable def movingArithmeticRootCuts (nodes : List MovingFormulaNode)
    (a : Bool → ℤ) (coord : Bool) : Finset ℝ :=
  nodes.toFinset.biUnion fun f => polynomialRootCuts (f.guard.polynomials a coord)

theorem movingArithmeticPeriod_pos (nodes : List MovingFormulaNode)
    (hfreq : ∀ f ∈ nodes, f.guard.right ≠ 0 ∧ f.guard.root ≠ 0) :
    0 < movingArithmeticPeriod nodes := by
  induction nodes with
  | nil => simp [movingArithmeticPeriod]
  | cons f nodes ih =>
    have hf := hfreq f (by simp)
    have hn := ih (fun g hg => hfreq g (List.mem_cons_of_mem _ hg))
    exact Nat.mul_pos (f.residuePeriod_pos hf.1 hf.2) hn

theorem movingArithmeticPeriod_dvd (nodes : List MovingFormulaNode)
    (f : MovingFormulaNode) (hf : f ∈ nodes) : f.residuePeriod ∣ movingArithmeticPeriod nodes :=
  List.dvd_prod (List.mem_map.mpr ⟨f, hf, rfl⟩)

theorem movingArithmeticRootCuts_mem (nodes : List MovingFormulaNode)
    (a : Bool → ℤ) (coord : Bool) (f : MovingFormulaNode) (hf : f ∈ nodes)
    (j : Fin 3) (x : ℝ) (hx : x ∈ (f.guard.polynomials a coord j).roots) :
    x ∈ movingArithmeticRootCuts nodes a coord := by
  apply Finset.mem_biUnion.mpr
  refine ⟨f, List.mem_toFinset.mpr hf, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hx⟩

/-- A concrete cardinality budget for the constructed root cuts. -/
theorem movingArithmeticRootCuts_card (nodes : List MovingFormulaNode)
    (a : Bool → ℤ) (coord : Bool) :
    (movingArithmeticRootCuts nodes a coord).card ≤
      ∑ f ∈ nodes.toFinset, ∑ j : Fin 3, (f.guard.polynomials a coord j).natDegree := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum (fun f _ => polynomialRootCuts_card (f.guard.polynomials a coord))

/-- The complete node support is constant on the explicitly constructed
root and residue cells. It is the actual arithmetic support, not an assumed
regularity property of the coefficient. -/
theorem movingFormulaNodes_holds_invariant (nodes : List MovingFormulaNode)
    (a : Bool → ℤ) (coord : Bool) (z w : ℤ)
    (hres : ∀ i, movingGiantUpdate a coord z i ≡ movingGiantUpdate a coord w i
      [ZMOD movingArithmeticPeriod nodes])
    (hcell : rootCellCode (movingArithmeticRootCuts nodes a coord) (z : ℝ) =
      rootCellCode (movingArithmeticRootCuts nodes a coord) (w : ℝ)) :
    (∀ f ∈ nodes, f.guard.ValidAt (movingGiantUpdate a coord z) ∧
      f.newGiant.IntegralAt (movingGiantUpdate a coord z)) ↔
    (∀ f ∈ nodes, f.guard.ValidAt (movingGiantUpdate a coord w) ∧
      f.newGiant.IntegralAt (movingGiantUpdate a coord w)) := by
  apply forall_congr'
  intro f
  apply imp_congr_right
  intro hf
  rw [f.holds_polynomials, f.holds_polynomials]
  have hres' := f.residueTests_modEq (movingGiantUpdate a coord z) (movingGiantUpdate a coord w)
    (fun i => (hres i).of_dvd (by exact_mod_cast movingArithmeticPeriod_dvd nodes f hf))
  apply and_congr hres'
  apply and_congr Iff.rfl
  apply forall_congr'
  intro j
  exact polynomial_nonneg_iff_of_root_cell (f.guard.polynomials a coord j)
    (movingArithmeticRootCuts nodes a coord)
    (movingArithmeticRootCuts_mem nodes a coord f hf j) hcell

end Ostmann

end OAI
