import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedRieszInterior

namespace OAI

/-!
# Capped Riesz kernels

Capping the radial singularity gives a continuous bounded vector kernel agreeing
with the Riesz kernel away from the cap. The scalar difference from hard truncation
is controlled by a symmetric weight supported on close pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def cappedRieszKernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) : Ambient d :=
  cappedInverseDistancePow (m + 1) ε q • (q.1 - q.2)

theorem cappedRieszKernel_continuous {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (cappedRieszKernel (d := d) m ε) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hc := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  exact hc.smul (continuous_fst.sub continuous_snd)

theorem cappedRieszKernel_norm_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) : ‖cappedRieszKernel m ε q‖ ≤ (ε ^ m)⁻¹ := by
  rw [cappedRieszKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _), ← dist_eq_norm, mul_comm]
  exact distance_mul_cappedInverseDistancePow_bound m ε hε q

theorem cappedRieszKernel_eq_kernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) (hq : ε ≤ dist q.1 q.2) :
    cappedRieszKernel m ε q = kernel m q.1 q.2 := by
  unfold cappedRieszKernel cappedInverseDistancePow
  rw [max_eq_right hq]
  simp only [kernel, dist_eq_norm]

def scalarCappedRieszKernel {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ := inner ℝ e (cappedRieszKernel m ε q)

theorem scalarCappedRieszKernel_continuous {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) : Continuous (scalarCappedRieszKernel m e ε) :=
  continuous_const.inner (cappedRieszKernel_continuous m ε hε)

theorem scalarCappedRieszKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarCappedRieszKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (cappedRieszKernel m ε q)| ≤ ‖e‖ * ‖cappedRieszKernel m ε q‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (cappedRieszKernel m ε q)
  exact hi.trans (mul_le_mul_of_nonneg_left (cappedRieszKernel_norm_bound m ε hε q) (norm_nonneg e))

def closedNearCapWeight {d : ℕ} (m : ℕ) (ε : ℝ) : Ambient d × Ambient d → ℝ :=
  (nearPairSet ε).indicator (fun _ => (ε ^ m)⁻¹)

theorem closedNearCapWeight_measurable {d : ℕ} (m : ℕ) (ε : ℝ) :
    Measurable (closedNearCapWeight (d := d) m ε) :=
  measurable_const.indicator (nearPairSet_measurable ε)

theorem closedNearCapWeight_nonneg {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) : 0 ≤ closedNearCapWeight m ε q :=
  indicator_nonneg (fun _ _ => inv_nonneg.mpr (pow_nonneg hε.le m)) q

theorem closedNearCapWeight_symm {d : ℕ} (m : ℕ) (ε : ℝ) (x y : Ambient d) :
    closedNearCapWeight m ε (y, x) = closedNearCapWeight m ε (x, y) := by
  simp only [closedNearCapWeight, indicator_apply, nearPairSet, mem_ofPred_eq, mem_closedBall]
  simp only [dist_comm x y]

theorem scalarCappedRieszKernel_hard_error {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q| ≤
      ‖e‖ * closedNearCapWeight m ε q := by
  by_cases hq : ε < dist q.1 q.2
  · have hnot : q ∉ nearPairSet ε := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm q.2 q.1, not_le] using! hq
    rw [scalarCappedRieszKernel, cappedRieszKernel_eq_kernel m ε q hq.le,
      scalarTruncatedKernel, ite_eq_left hq, sub_self, abs_zero,
      closedNearCapWeight, indicator_of_notMem hnot, mul_zero]
  · have hyes : q ∈ nearPairSet ε := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm q.2 q.1] using! le_of_not_gt hq
    rw [scalarTruncatedKernel, ite_eq_right hq, sub_zero, closedNearCapWeight, indicator_of_mem hyes]
    exact scalarCappedRieszKernel_bound m e ε hε q

end

end RieszRectifiability

end OAI
