import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Find

namespace OAI

/-! # Slowly shrinking good sets with subexponential mass -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Countably many eventual properties can be followed at a slowly
increasing index. This is used only for the shrinking profile neighborhoods. -/
theorem exists_slow_eventual_selection (P : ℕ → ℝ → Prop)
    (hP : ∀ j, ∀ᶠ r in atTop, P j r) :
    ∃ k : ℝ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ r in atTop, P (k r) r := by
  classical
  choose N hN using fun j => eventually_atTop.mp (hP j)
  let k : ℝ → ℕ := fun r => Nat.findGreatest (fun j => N j ≤ r) ⌊r⌋₊
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (N j), eventually_ge_atTop (j : ℝ)] with r hr hj
    exact Nat.le_findGreatest (Nat.le_floor hj) hr
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop (N 0)] with r hr
  exact hN (k r) r (Nat.findGreatest_spec (P := fun j => N j ≤ r)
    (n := ⌊r⌋₊) (m := 0) (Nat.zero_le _) hr)

/-- If every fixed good set has a positive eventual mass, the good set can
shrink to its limiting profile slowly enough that its mass is `exp(-o(r))`. -/
theorem exists_slow_subexponential_mass (mass : ℕ → ℝ → ℝ)
    (hmass : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, c ≤ mass j r) :
    ∃ k : ℝ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBound (fun r => mass (k r) r) := by
  have hgood (j : ℕ) : ∀ᶠ r in atTop,
      Real.exp (-(1 / ((j : ℝ) + 1)) * r) ≤ mass j r := by
    obtain ⟨c, hc, he⟩ := hmass j
    filter_upwards [(subexponential_lower_const hc) (1 / ((j : ℝ) + 1)) (by positivity), he]
      with r hr hs
    exact hr.trans hs
  obtain ⟨k, hk, he⟩ := exists_slow_eventual_selection _ hgood
  refine ⟨k, hk, ?_⟩
  intro ε hε
  have ht : Tendsto (fun r => 1 / ((k r : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  filter_upwards [he, ht.eventually (eventually_lt_nhds hε), eventually_ge_atTop (0 : ℝ)]
    with r hr hsmall hpos
  apply le_trans _ hr
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hsmall.le) hpos

end PolycyclicRecognition

end

end OAI
