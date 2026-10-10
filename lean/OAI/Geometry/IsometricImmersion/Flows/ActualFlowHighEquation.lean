import OAI.Geometry.IsometricImmersion.Darboux.ActualHighDrift

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted

theorem actual_flow_high_equation
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (m : ℕ) {p : Coord}
    (hp : p ∈ capChartDomain) :
    multiplierOperator (heightChartA g z Y) (heightChartB g z Y (m + 3))
      (heightChartC g z Y (m + 3)) (capPullback Y (verticalJet z (m + 3))) p =
      capPullback Y (actualHighRemainder g z m) p := by
  rw [← height_coefficient_operator_transport hg hU hz hyy hY hode hvar hmap
    (verticalJet_contDiffOn hU hz (m + 3)) hp (m + 3)]
  exact actual_differentiated_drift hg hU hz hD hyy m (hmap hp)

theorem patch_actual_flow_high_equation
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (h : PatchAdmissibleHeight g z)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (m : ℕ) {p : Coord} (hp : p ∈ capChartDomain) :
    multiplierOperator (heightChartA g z Y) (heightChartB g z Y (m + 3))
      (heightChartC g z Y (m + 3)) (capPullback Y (verticalJet z (m + 3))) p =
      capPullback Y (actualHighRemainder g z m) p := by
  obtain ⟨U, hU, hSU, hg, hz, hD, hE, hyy, hq⟩ := h
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgo : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  exact actual_flow_high_equation hgo modelOpenSquare_isOpen (hz.mono hOU)
    (fun p hp => hD p (modelOpenSquare_subset hp))
    (fun p hp => hyy p (modelOpenSquare_subset hp)) hY hode hvar
    (fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)) m hp

end SmoothLocal.HighEquation

end

end OAI
