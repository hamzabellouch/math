import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace OAI

/-! # Compact metric cutoffs for controlled Følner pairs -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set MeasureTheory

variable {X : Type*} [MetricSpace X]

def metricTent (S : Set X) (r : ℝ) (x : X) : ℝ := max (1 - infDist x S / r) 0

theorem metricTent_nonneg (S : Set X) (r : ℝ) (x : X) : 0 ≤ metricTent S r x :=
  le_max_right _ _

theorem metricTent_le_one (S : Set X) {r : ℝ} (hr : 0 < r) (x : X) :
    metricTent S r x ≤ 1 := by
  apply max_le _ zero_le_one
  have := div_nonneg (infDist_nonneg : 0 ≤ infDist x S) hr.le
  linarith

theorem metricTent_eq_one {S : Set X} (r : ℝ) {x : X} (hx : x ∈ S) :
    metricTent S r x = 1 := by simp [metricTent, infDist_zero_of_mem hx]

theorem continuous_metricTent (S : Set X) (r : ℝ) : Continuous (metricTent S r) :=
  (continuous_const.sub ((continuous_infDist_pt S).div_const r)).max continuous_const

theorem abs_metricTent_sub_le (S : Set X) {r : ℝ} (hr : 0 < r) (x y : X) :
    |metricTent S r x - metricTent S r y| ≤ dist x y / r := by
  calc
    _ ≤ |(1 - infDist x S / r) - (1 - infDist y S / r)| :=
      abs_max_sub_max_le_abs _ _ 0
    _ = |infDist x S - infDist y S| / r := by
      have he : (1 - infDist x S / r) - (1 - infDist y S / r) =
          -(infDist x S - infDist y S) / r := by ring
      rw [he, abs_div, abs_neg, abs_of_pos hr]
    _ ≤ dist x y / r := div_le_div_of_nonneg_right
      (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (lipschitz_infDist_pt S).dist_le_mul x y) hr.le

theorem metricTent_support_subset {S : Set X} (hS : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    Function.support (metricTent S r) ⊆ cthickening r S := by
  intro x hx
  have hpos : 0 < metricTent S r x := lt_of_le_of_ne
    (metricTent_nonneg S r x) (Ne.symm hx)
  have hd : infDist x S < r := by
    have h : 0 < 1 - infDist x S / r := (lt_max_iff.mp hpos).resolve_right (lt_irrefl 0)
    exact (div_lt_one hr).mp (by linarith)
  exact thickening_subset_cthickening r S ((mem_thickening_iff_infDist_lt hS).2 hd)

theorem metricTent_compact_support [ProperSpace X] {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (metricTent S r) :=
  (hS.cthickening (r := r)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (metricTent_support_subset hne hr) isClosed_cthickening)

variable [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem metricTent_integral_lower {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : ℝ} (hr : 0 < r) : μ.real S ≤ ∫ x, metricTent S r x ∂μ := by
  have hi := (continuous_metricTent S r).integrable_of_hasCompactSupport
    (metricTent_compact_support hS hne hr) (μ := μ)
  calc
    μ.real S = ∫ x in S, metricTent S r x ∂μ := by
      rw [setIntegral_congr_fun hS.measurableSet (fun x hx => metricTent_eq_one r hx)]
      simp
    _ ≤ ∫ x, metricTent S r x ∂μ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (metricTent_nonneg S r))

end PolycyclicRecognition

end

end OAI
