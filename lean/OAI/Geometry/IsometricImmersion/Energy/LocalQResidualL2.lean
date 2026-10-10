import OAI.Geometry.IsometricImmersion.Darboux.QFirstSpatialBounds
import OAI.Geometry.IsometricImmersion.Darboux.QEnergyApplication

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem HorizontalMetricTwoJetBound.mono_order
    {g : MetricField} {p : Coord} {N M : ℕ} {G : ℝ}
    (h : HorizontalMetricTwoJetBound g p N G) (hMN : M ≤ N) :
    HorizontalMetricTwoJetBound g p M G :=
  ⟨fun i j n hn => h.1 i j n (hn.trans hMN),
    fun d i j n hn => h.2.1 d i j n (hn.trans hMN),
    fun d e i j n hn => h.2.2 d e i j n (hn.trans hMN)⟩

theorem exists_same_slice_actual_Q_source_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (B : ℝ≥0∞) := by
  obtain ⟨C, hC, hOuter⟩ := exists_same_region_active_Q_coefficient_bound G R Z hG hR hd hc m
  obtain ⟨Cfirst, hCfirst, hFirst⟩ := exists_same_region_Q_first_xi_bound G R Z hG hR hd hc
  let budget := qRemainderSliceBudget C Cfirst lengthFloor 0 width H m
  have hbudget : budget < (⊤ : ℝ≥0∞) := qRemainderSliceBudget_lt_top C Cfirst lengthFloor 0 width H m
  refine ⟨budget.toNNReal, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have houter := hOuter g z U S hg hU hSU hcoords hgB hz2 hdet hden
  have hfirst := hFirst g z U S hg hU hz hSU hcoords
    (fun p hp => (hgB p hp).mono_order (by omega)) hzB hdet hden
  rw [ENNReal.coe_toNNReal hbudget.ne]
  exact (actualQHighRemainder_slice_eLpNorm_two_active hg hU hz hxx
    (fun x hx => hSU (hseg x hx)) hlen hwidth hm hC hCfirst hL2
    (fun w hw r hr x hx => houter w hw r hr _ (hseg x hx))
    (fun x hx => hfirst 2 (by decide) _ (hseg x hx))
    (fun x hx => hfirst 3 (by decide) _ (hseg x hx))).trans
      (qRemainderSliceBudget_mono_width H m hupper)

theorem exists_same_slice_actual_Q_source_norm_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      Real.sqrt (∫ x in left..right, actualQHighRemainder g z m (coordinatePoint x theta)^2) ≤ (B : ℝ) := by
  obtain ⟨B, hB⟩ := exists_same_slice_actual_Q_source_bound G R Z lengthFloor width H hG hR hlen hd hc m hm
  refine ⟨B, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hn := hB g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hmem := actualQHighRemainder_slice_memLp_two hg hU hz hxx m (fun x hx => hSU (hseg x hx))
  have hlr : left ≤ right := by linarith
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    sqrt_integral_square_eq_L2_norm hmem, Lp.norm_def, eLpNorm_congr_ae hmem.coeFn_toLp]
  exact ENNReal.toReal_mono (by simp : (B : ℝ≥0∞) ≠ ⊤) hn

end SmoothLocal.HighEquation

end

end OAI
