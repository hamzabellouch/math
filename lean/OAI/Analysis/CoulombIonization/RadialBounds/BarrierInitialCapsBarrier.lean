import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialBoundsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set MeasureTheory

namespace CoulombBarrier
open CoulombAnalysis

lemma initializedBarrier_exterior {Z B r a : ℝ} {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) :
    initializedBarrier Z B r a ρ x =
      if ‖x‖ < 2*r then max (initialBranch Z r a ρ x) (outerBarrier B r x)
      else outerBarrier B r x := by
  unfold initializedBarrier initializedOffset cutMaximum
  rw [ite_eq_right (not_lt.mpr hx)]
  split_ifs
  · rw [add_max,nuclear_outerOffset_eq hx]
    rfl
  · exact nuclear_outerOffset_eq hx

lemma initializedBarrier_lower {Z B r a : ℝ} {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) : outerBarrier B r x ≤ initializedBarrier Z B r a ρ x := by
  rw [initializedBarrier_exterior hx]
  split_ifs
  · exact le_max_right _ _
  · exact le_refl _

lemma initializedBarrier_cap {Z B C r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ Z/(20*r))
    (hCB : B ≤ C) (hCZ : 32*Z*r^3 ≤ C) {ρ : TFSpace → ℝ}
    (hn : ∀ x, 0 ≤ ρ x) {x : TFSpace} (hx : r ≤ ‖x‖) :
    initializedBarrier Z B r a ρ x ≤ C/‖x‖^4 := by
  rw [initializedBarrier_exterior hx]
  have hb : outerBarrier B r x ≤ C/‖x‖^4 :=
    (outerBarrier_bounds hB hr hx).2.trans (div_le_div_of_nonneg_right hCB (by positivity))
  split_ifs with h2
  · exact max_le (initial_branch_cap hZ hr ha hquad hCZ hx h2.le
      (tfPotential_nonneg (ae_of_all _ hn) x)) hb
  · exact hb

lemma initializedBarrier_tail {Z B r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ Z/(20*r))
    {ρ : TFSpace → ℝ} (hn : ∀ x, 0 ≤ ρ x) {x : TFSpace}
    (hx : (19/10)*r < ‖x‖) : initializedBarrier Z B r a ρ x = outerBarrier B r x := by
  have hx0 : r ≤ ‖x‖ := by linarith
  rw [initializedBarrier_exterior hx0]
  split_ifs with h2
  · have hv := initial_branch_negative hZ hr ha hquad hx h2.le (tfPotential_nonneg (ae_of_all _ hn) x)
    have hb := (outerBarrier_bounds hB hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    exact max_eq_right (by linarith)
  · rfl

end CoulombBarrier

end

end OAI
