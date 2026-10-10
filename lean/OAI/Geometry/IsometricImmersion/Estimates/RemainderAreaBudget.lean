import OAI.Geometry.IsometricImmersion.Caps.CapL2Basics
import OAI.Geometry.IsometricImmersion.Energy.FixedMetricMixedL2
import OAI.Geometry.IsometricImmersion.Metrics.FixedMetricRemainder

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

theorem chainProductL2Budget_mono_area (B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) :
    chainProductL2Budget B H V ell ≤ chainProductL2Budget B H W ell :=
  mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hVW (by norm_num : 0 ≤ (1 / (2 : ℝ)))))

theorem chainWordL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w ≤ chainWordL2Budget C B H W ell w := by
  apply Finset.sum_le_sum
  intro _ _
  exact mul_le_mul' le_rfl (chainProductL2Budget_mono_area B H hVW ell)

theorem chainSumL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws ≤ chainSumL2Budget C B H W ell ws := by
  induction ws with
  | nil => exact le_rfl
  | cons word _ ih => exact add_le_add (chainWordL2Budget_mono_area C B H hVW ell word) ih

theorem actualHighRemainderL2Budget_mono_area (C Cfirst B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m ≤ actualHighRemainderL2Budget C Cfirst B H W m :=
  add_le_add (chainSumL2Budget_mono_area C B H hVW (m+3) (topResidualWords m)) le_rfl

theorem mixedRemainderL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (k : ℕ) :
    mixedRemainderL2Budget C B H V k ≤ mixedRemainderL2Budget C B H W k := by
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro composition _
  exact chainWordL2Budget_mono_area C B H hVW k ⟨composition.length, composition.partSize⟩

theorem mixedXBudget_mono_remainder (C : ℝ) {R S : ℝ≥0∞} (hRS : R ≤ S)
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n ≤ mixedXBudget C S Htop n := by
  induction n with
  | zero => exact add_le_add le_rfl hRS
  | succ _ ih => exact mul_le_mul' le_rfl ih

def uniformMixedOrderBudget (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) : ℝ≥0 :=
  max H (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N).toNNReal

theorem uniformMixedOrderBudget_coe (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) :
    (uniformMixedOrderBudget C B H Htop N : ℝ≥0∞) =
      max (H : ℝ≥0∞) (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N) := by
  unfold uniformMixedOrderBudget
  rw [ENNReal.coe_max, ENNReal.coe_toNNReal
    (mixedXBudget_lt_top C
      (mixedRemainderL2Budget_lt_top C B H modelSquare_isCompact.measure_lt_top (N-2)) Htop N).ne]

theorem coordinateL2Bound_order_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVS : V ⊆ modelSquare)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N-2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N-3) B)
    (hheight : CoordinateL2Bound z V (N-1) H)
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N-1))) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞)) :
    CoordinateL2Bound z V N (uniformMixedOrderBudget C B H Htop N) := by
  have hmeas (word : List (Fin 2)) :
      AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V) :=
    ((orderedPartial_contDiffOn hz hU word).continuousOn.mono
      hVU).aestronglyMeasurable (μ := volume) hV
  intro ds hds
  rw [uniformMixedOrderBudget_coe]
  by_cases hloworder : ds.length ≤ N-1
  · exact (hheight ds hloworder).trans (le_max_left _ _)
  · have hlen : ds.length = N := by omega
    have hhigh := all_orderN_mixed_eLpNorm_two hg hU hz hD hyy hV hVU hN hC hB hP hlow
      (fun word hword => hheight.eLpNorm_le word hword (hmeas word)) hv hxv ds hlen
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hmeas ds),
      ENNReal.toReal_ofNat] at hhigh
    exact (hhigh.trans (mixedXBudget_mono_remainder C
        (mixedRemainderL2Budget_mono_area C B H (measure_mono hVS) (N-2)) Htop N)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
