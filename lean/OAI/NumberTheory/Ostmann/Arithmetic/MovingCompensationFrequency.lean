import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantIntervalBridge

namespace OAI

/-! # The actual compensation tuple satisfies the integer frequency scale -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiant_integer_cell_lower (G : ℝ) (p : ℕ)
    (hp : p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊) :
    Real.exp (G - 1) < (p : ℝ) :=
  (Nat.floor_lt (Real.exp_nonneg _)).mp (Finset.mem_Ioc.mp hp).1

/-- This discharges the scale premise for the original, unconditioned
compensation draw and every integer in the full outer cell. -/
theorem movingProductNaturalCutoff_compensation_scale {σ : Type} [Fintype σ]
    (value : σ → ℕ) (μ : ℕ → σ → ℝ) (G c : ℕ → ℝ)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (W Y m : ℝ) (hm : 64 ≤ m) (hY : Y ≤ W)
    (hgap : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (n : ℕ) (hH : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (p : ℕ) (hp : Real.exp (G (n + 1) - 1) ≤ (p : ℝ)) :
    2 * movingProductNaturalCutoff (movingCellPivotExponent G c) W Y m n *
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ ≤
      movingProductNaturalCutoff (movingCellPivotExponent G c) W Y m (n + 1) *
        (p * ∏ i, value (u i)) := by
  let a := (movingTemplateCompensationEquiv σ n).symm u
  have he : movingTemplateCompensationEquiv σ n a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ n) n a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  have hlower := movingCompensation_pivot_lower_of_bound value (μ n) (c n) (G (n + 1))
    (hμ n) n a ha p hp
  rw [movingTemplateCompensationEquiv_product, he] at hlower
  exact movingProductNaturalCutoff_scale (movingCellPivotExponent G c) W Y m n hm hY
    hgap hH (p * ∏ i, value (u i)) hlower

end Ostmann

end OAI
