import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace OAI

namespace Ostmann
open MeasureTheory Set
open scoped SchwartzMap ContDiff

noncomputable def smoothPartition (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

@[fun_prop] theorem smoothPartition_contDiff : ContDiff ℝ ∞ smoothPartition := by
  unfold smoothPartition
  fun_prop

@[fun_prop] theorem smoothPartition_continuous : Continuous smoothPartition :=
  smoothPartition_contDiff.continuous

theorem smoothPartition_nonneg (x : ℝ) : 0 ≤ smoothPartition x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem smoothPartition_le_one (x : ℝ) : smoothPartition x ≤ 1 := by
  have h₁ := Real.smoothTransition.le_one (x + 1)
  have h₂ := Real.smoothTransition.nonneg x
  unfold smoothPartition
  linarith

theorem smoothPartition_zero_of_le_neg_one {x : ℝ} (hx : x ≤ -1) :
    smoothPartition x = 0 := by
  rw [smoothPartition, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem smoothPartition_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    smoothPartition x = 0 := by
  rw [smoothPartition, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hx, sub_self]

theorem smoothPartition_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    smoothPartition x = 0 := by
  rcases le_abs.mp hx with h | h
  · exact smoothPartition_zero_of_one_le h
  · exact smoothPartition_zero_of_le_neg_one (by linarith)

theorem smoothPartition_support_subset : Function.support smoothPartition ⊆ Ioo (-1) 1 := by
  intro x hx
  have hn : smoothPartition x ≠ 0 := hx
  constructor
  · by_contra h
    exact hn (smoothPartition_zero_of_le_neg_one (le_of_not_gt h))
  · by_contra h
    exact hn (smoothPartition_zero_of_one_le (le_of_not_gt h))

theorem smoothPartition_hasCompactSupport : HasCompactSupport smoothPartition :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (smoothPartition_support_subset.trans Ioo_subset_Icc_self)

noncomputable def smoothPartitionSchwartz : 𝓢(ℝ, ℝ) :=
  smoothPartition_hasCompactSupport.toSchwartzMap smoothPartition_contDiff

@[simp] theorem smoothPartitionSchwartz_apply (x : ℝ) :
    smoothPartitionSchwartz x = smoothPartition x := rfl

theorem smoothPartition_integrable : Integrable smoothPartition :=
  smoothPartition_continuous.integrable_of_hasCompactSupport smoothPartition_hasCompactSupport

end Ostmann

end OAI
