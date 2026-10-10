import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartHeight

namespace OAI

/-! # Polynomial size and exact height of a scaled word-chart pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

def wordChartPivot {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I] (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (r : ℝ) (z : Fin (finrank ℝ L) → ℝ) : L :=
  (exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
    (max (Real.log r) 0)).equivFun.symm z

/-- The pivot logarithm has one fixed polynomial envelope in the physical
scale, for the actual fixed word chart and coordinate. -/
theorem wordChartPivot_polynomial_bound {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (z : Fin (finrank ℝ L) → ℝ) :
    ∃ A : ℝ, ∃ p : ℕ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      ‖b₀.equivFun (wordChartPivot X S β r z)‖ ≤ A * (1 + r) ^ p := by
  let b := WordBasisSelections.basis X S β
  let p := ∑ j, bracketWordLength (β.val j : FreeMagma I)
  let A := (∑ j, ‖b₀.equivFun (b j)‖) * ‖z‖
  refine ⟨A, p, by dsimp [A]; positivity, ?_⟩
  intro r hr
  have hh := norm_polynomial_chart_log_le b b₀
    (fun j => bracketWordLength (β.val j : FreeMagma I)) p
    (fun j => by
      dsimp only [p]
      exact Finset.single_le_sum (f := fun j => bracketWordLength (β.val j : FreeMagma I)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hr z
  simpa only [wordChartPivot, bracketWordExponent_one, max_eq_left (Real.log_nonneg hr)] using hh

/-- The pivot's height is exactly linear in physical scale. -/
theorem wordChartPivot_height {L W I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 1 ≤ r) (z : Fin (finrank ℝ L) → ℝ) :
    h (wordChartPivot X S β r z) =
      r • h ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  simpa only [wordChartPivot, bracketWordExponent_one, max_eq_left (Real.log_nonneg hr)] using
    word_length_chart_height X S β h hh (lt_of_lt_of_le zero_lt_one hr) z

end PolycyclicRecognition

end

end OAI
