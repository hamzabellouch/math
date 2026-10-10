import OAI.Geometry.IsometricImmersion.Caps.EllipticCutoff
import OAI.Geometry.IsometricImmersion.Flows.FlowTransport
import OAI.Geometry.IsometricImmersion.Coordinates.PatchGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capOuterSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  capSpatialCutoff (capOuterEdge L) (-capOuterEdge (-R)) (capOuterEdge A)

theorem capOuterSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capOuterSpatialCutoff L R A) :=
  capSpatialCutoff_contDiff _ _ _

theorem capOuterSpatialCutoff_range (L R A : ℝ) (p : Coord) :
    0 ≤ capOuterSpatialCutoff L R A p ∧ capOuterSpatialCutoff L R A p ≤ 1 :=
  capSpatialCutoff_range _ _ _ p

theorem capSpatialCutoff_nonzero_bounds {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) :
    capOuterEdge L < p 0 ∧ p 0 < -capOuterEdge (-R) ∧ capOuterEdge A < p 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  have hz (h : p 0 ≤ capOuterEdge L ∨ -capOuterEdge (-R) ≤ p 0 ∨
      p 1 ≤ capOuterEdge A) : capSpatialCutoff L R A p = 0 :=
    threeEdgeCutoff_zero hli (neg_lt_neg hri) hai p h
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hp (hz (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hp (hz (Or.inr (Or.inl (le_of_not_gt h))))
  · by_contra h
    exact hp (hz (Or.inr (Or.inr (le_of_not_gt h))))

theorem capOuterSpatialCutoff_one_of_nonzero {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) : capOuterSpatialCutoff L R A p = 1 := by
  have hlo := (capEdges_bounds hL).1
  have hro := (capEdges_bounds (x := -R) (by linarith)).1
  have hao := (capEdges_bounds hA).1
  obtain ⟨htl, htr, hsb⟩ := capSpatialCutoff_nonzero_bounds hL hR hA hp
  exact capSpatialCutoff_one hlo (by linarith) hao p ⟨htl.le, htr.le, hsb.le⟩

theorem capSpatialCutoff_nonzero_of_partial {L R A : ℝ} {p : Coord} {i : Fin 2}
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    capSpatialCutoff L R A p ≠ 0 := by
  intro hz
  have hmin : IsLocalMin (capSpatialCutoff L R A) p := by
    change ∀ᶠ q in 𝓝 p, capSpatialCutoff L R A p ≤ capSpatialCutoff L R A q
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [hz] using (capSpatialCutoff_range L R A q).1)
  have hd := hmin.fderiv_eq_zero
  exact hp (by simp [coordPartial, hd])

theorem capOuterSpatialCutoff_one_of_partial {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord} {i : Fin 2}
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    capOuterSpatialCutoff L R A p = 1 :=
  capOuterSpatialCutoff_one_of_nonzero hL hR hA (capSpatialCutoff_nonzero_of_partial hp)

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem modelCurvature_lower_flow_bottom {kappa : ℝ} (hk : 0 < kappa)
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) (hs : p 1 < -3 / 2) :
    kappa < modelCurvature kappa (capChart Y p) := by
  have hy : capFlowHeight Y p < -(37 / 25 : ℝ) := by
    linarith [(abs_le.mp hdisp).2]
  have hy2 : 2 < (capFlowHeight Y p)^2 := by
    nlinarith [sq_nonneg (capFlowHeight Y p + 37 / 25)]
  have hh := modelProfile_eq_one_sub_sq (y := capFlowHeight Y p) (by linarith)
  unfold modelCurvature
  rw [capChart_zero, capChart_one, hh]
  have hbase : 1 < (p 0)^2 - (1 - (capFlowHeight Y p)^2) := by
    nlinarith [sq_nonneg (p 0)]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hbase hk

theorem capChart_not_mem_patchBox_of_cutoff_band
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hband : (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2)) :
    capChart Y p ∉ patchBox := by
  intro hin
  rcases hband with ht | hs
  · have hxlo := hin.1 0
    have hxhi := hin.2 0
    simp only [capChart_zero] at hxlo hxhi
    have habs : |p 0| ≤ (1 : ℝ) / 10 := abs_le.mpr ⟨hxlo, hxhi⟩
    linarith [ht.1]
  · have hylo := hin.1 1
    simp only [capChart_one] at hylo
    linarith [hs.2, (abs_le.mp hdisp).2]

theorem capSpatialCutoff_partial_actual_curvature_lower
    {g0 eta : MetricField} {kappa L R A : ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {i : Fin 2}
    (hk : 0 < kappa) (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    kappa < capPullback Y (gaussianCurvature (g0 + eta)) p := by
  have hband := capSpatialCutoff_derivative_bands hL hR hA p i hpartial
  have hnot := capChart_not_mem_patchBox_of_cutoff_band hdisp hband
  have hts : capChart Y p ∉ tsupport eta := fun h => hnot (hsupport h)
  have hsame := gaussianCurvature_eq_of_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  change kappa < gaussianCurvature (g0 + eta) (capChart Y p)
  rw [hsame, hbackground _ hpU]
  rcases hband with ht | hs
  · have hh := modelCurvature_lateral_band_lower hk (p := capChart Y p)
      (by simpa only [capChart_zero] using ht.1)
    linarith
  · exact modelCurvature_lower_flow_bottom hk hdisp hs.2

end SmoothLocal.Flow

end

end OAI
