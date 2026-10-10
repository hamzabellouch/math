import OAI.Geometry.IsometricImmersion.Flows.FlowHeightCoefficients

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem height_jetEnergy_first_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U := by
  have h0 := partial_contDiffOn hz hU 0
  have h1 := partial_contDiffOn hz hU 1
  fin_cases i
  · have hf : ContDiffOn ℝ ∞ (fun p => -2 * g p 1 1 * coordPartial 0 z p +
        (g p 0 1 + g p 1 0) * coordPartial 1 z p) U :=
      ((contDiffOn_const.mul (hg.1 1 1)).mul h0).add (((hg.1 0 1).add (hg.1 1 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_zero, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 0
  · have hf : ContDiffOn ℝ ∞ (fun p => (g p 0 1 + g p 1 0) * coordPartial 0 z p -
        2 * g p 0 0 * coordPartial 1 z p) U :=
      (((hg.1 0 1).add (hg.1 1 0)).mul h0).sub ((contDiffOn_const.mul (hg.1 0 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 1

theorem height_christoffelAlongD_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  have hf : ContDiffOn ℝ ∞ (fun p => christoffel g i 0 0 p -
      2 * hessianQuotient g z p * christoffel g i 0 1 p +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p) U :=
    ((christoffel_contDiffOn hg hU i 0 0).sub
      ((contDiffOn_const.mul hq).mul (christoffel_contDiffOn hg hU i 0 1))).add
      ((hq.pow 2).mul (christoffel_contDiffOn hg hU i 1 1))
  exact hf.congr (fun p hp => christoffelAlongD_eq hg hU hp _ i)

theorem heightPFirst_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (heightPFirst g z i) U := by
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hf : ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1)^2)) U :=
    (height_christoffelAlongD_contDiffOn hg hU hz hyy i).add
      ((gaussianCurvature_contDiffOn hg hU).mul
        (((height_jetEnergy_first_contDiffOn hg hU hz i).div hh hyy).add
          (((heightEnergy_contDiffOn hg hU hz).mul (christoffel_contDiffOn hg hU i 1 1)).div
            (hh.pow 2) (fun p hp => pow_ne_zero 2 (hyy p hp)))))
  exact hf.congr (fun p hp => heightPFirst_eq hg hU hp (hyy p hp) i)

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalB g z ell) U :=
  (heightPFirst_contDiffOn hg hU hz hyy 0).neg.sub
    (contDiffOn_const.mul (partial_contDiffOn (hessianQuotient_contDiffOn hg hU hz hyy) hU 1))

theorem heightChartB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain :=
  capPullback_contDiffOn hY (heightOriginalB_contDiffOn hg hU hz hyy ell) hmap

end SmoothLocal.Flow

end

end OAI
