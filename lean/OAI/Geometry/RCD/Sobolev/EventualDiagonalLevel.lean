import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! # A slowly increasing level satisfying each prescribed eventual requirement -/

open Filter
noncomputable section
namespace RegularPointCoordinates

theorem exists_eventual_diagonal_level (P : ℕ → ℕ → Prop)
    (hP : ∀ m, ∀ᶠ k in atTop, P m k) :
    ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧ ∀ᶠ k in atTop, P (d k) k := by
  classical
  choose N hN using fun m => eventually_atTop.1 (hP m)
  let d : ℕ → ℕ := fun k => Nat.findGreatest (fun m => N m ≤ k) k
  have hd : Tendsto d atTop atTop := by
    refine tendsto_atTop.2 fun m => ?_
    filter_upwards [eventually_ge_atTop (max m (N m))] with k hk
    exact Nat.le_findGreatest ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk)
  refine ⟨d,hd,?_⟩
  filter_upwards [eventually_ge_atTop (N 0)] with k hk
  exact hN (d k) k (Nat.findGreatest_spec (P := fun m => N m ≤ k) (Nat.zero_le k) hk)

end RegularPointCoordinates

end

end OAI
