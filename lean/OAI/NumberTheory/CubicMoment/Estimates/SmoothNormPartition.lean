import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortFamily
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! An explicit finite smooth partition on every bounded positive norm range.
Its fixed weight is supported in `[1,2]`, as required by the smooth
short-factor estimates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def normPartitionStep (x : ℝ) : ℝ := Real.smoothTransition (3*(x-1))

def normPartitionWeight (x : ℝ) : ℂ :=
  (normPartitionStep x - normPartitionStep (3*x/4) : ℝ)

lemma normPartitionStep_zero {x : ℝ} (hx : x ≤ 1) : normPartitionStep x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma normPartitionStep_one {x : ℝ} (hx : 4/3 ≤ x) : normPartitionStep x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma normPartitionWeight_low {x : ℝ} (hx : x < 1) : normPartitionWeight x = 0 := by
  rw [normPartitionWeight,normPartitionStep_zero hx.le,
    normPartitionStep_zero (show 3*x/4 ≤ 1 by linarith)]
  simp

lemma normPartitionWeight_high {x : ℝ} (hx : 2 < x) : normPartitionWeight x = 0 := by
  rw [normPartitionWeight,normPartitionStep_one (show 4/3 ≤ x by linarith),
    normPartitionStep_one (show 4/3 ≤ 3*x/4 by linarith)]
  simp

lemma normPartitionWeight_norm (x : ℝ) : ‖normPartitionWeight x‖ ≤ 1 := by
  by_cases hx : x < 1
  · rw [normPartitionWeight_low hx,norm_zero]
    norm_num
  have hmono : normPartitionStep (3*x/4) ≤ normPartitionStep x :=
    Real.smoothTransition.monotone (by linarith)
  have hnonneg := Real.smoothTransition.nonneg (3*(3*x/4-1))
  have hone := Real.smoothTransition.le_one (3*(x-1))
  rw [normPartitionWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hmono)]
  dsimp [normPartitionStep] at *
  linarith

lemma normPartitionWeight_smooth : ContDiff ℝ ∞ normPartitionWeight := by
  unfold normPartitionWeight normPartitionStep
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).sub
      (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma normPartitionWeight_tsupport : tsupport normPartitionWeight ⊆ Icc 1 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (normPartitionWeight_low (lt_of_not_ge h))
  · by_contra h
    exact hx (normPartitionWeight_high (lt_of_not_ge h))

lemma normPartitionWeight_compact : HasCompactSupport normPartitionWeight :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) normPartitionWeight_tsupport

lemma normPartitionWeight_positive_support : tsupport normPartitionWeight ⊆ Ioi 0 := by
  intro x hx
  have := (normPartitionWeight_tsupport hx).1
  exact lt_of_lt_of_le zero_lt_one this

lemma normPartitionWeight_telescope (x : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, normPartitionWeight (x/(4/3:ℝ)^k)) =
      (normPartitionStep x - normPartitionStep (x/(4/3:ℝ)^N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,normPartitionWeight]
    have he : 3*(x/(4/3:ℝ)^N)/4 = x/(4/3:ℝ)^(N+1) := by
      rw [pow_succ]
      ring
    rw [he]
    push_cast
    ring

theorem normPartitionWeight_partition {B x : ℝ} {N : ℕ}
    (hx : 1 ≤ x) (hB : x ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k ∈ Finset.range N, normPartitionWeight (2*x/(4/3:ℝ)^k)) = 1 := by
  rw [normPartitionWeight_telescope,
    normPartitionStep_one (show 4/3 ≤ 2*x by linarith)]
  have hpow : 0 < (4/3:ℝ)^N := pow_pos (by norm_num) _
  rw [normPartitionStep_zero ((div_le_one hpow).mpr (by linarith))]
  norm_num

lemma normPartitionWeight_scale (k : ℕ) (x : ℝ) :
    normPartitionWeight (2*x/(4/3:ℝ)^k) =
      normPartitionWeight (x/((4/3:ℝ)^k/2)) := by
  congr 1
  field_simp

end CubicFirstMoment

end

end OAI
