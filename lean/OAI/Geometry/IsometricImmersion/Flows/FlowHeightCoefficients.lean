import OAI.Geometry.IsometricImmersion.Flows.FlowTransport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightOriginalA (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  gaussianCurvature g p * darbouxG g z p

def heightOriginalB (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  -heightPFirst g z 0 p - 2 * (ell : ℝ) * coordPartial 1 (hessianQuotient g z) p

def heightOriginalC0 (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
    hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p +
      (ell : ℝ) * coordPartial 1 (heightOriginalA g z) p

def heightChartA (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  capTransportA Y (heightOriginalA g z)

def heightChartB (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capPullback Y (heightOriginalB g z ell)

def heightChartC (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capTransportC Y (heightOriginalA g z) (heightOriginalC0 g z ell)

def heightChartG1 (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  capPullback Y (darbouxG g z) p * (capChartRho Y p) ^ 2

def heightChartRemainder (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ)
    (ell : ℕ) (p : Coord) : ℝ :=
  (capPullback Y (curvatureDriftError g z) p - capPullback Y (coordPartial 1 (darbouxG g z)) p) /
      (capPullback Y (darbouxG g z) p * capChartRho Y p) -
    (2 * (ell : ℝ) + 1) * capChartSigma Y p / (capChartRho Y p) ^ 2

variable {g : MetricField} {z u : Coord → ℝ} {U : Set Coord} {p : Coord} {Y : ℝ → ℝ → ℝ}

theorem heightOriginalA_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (heightOriginalA g z) U :=
  (gaussianCurvature_contDiffOn hg hU).mul (darbouxG_contDiffOn hg hU hz hyy)

theorem heightOriginalA_partial_y (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) :
    coordPartial 1 (heightOriginalA g z) p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * coordPartial 1 (darbouxG g z) p := by
  exact HessianCalculus.coordPartial_mul_at
    (((gaussianCurvature_contDiffOn hg hU).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (((darbouxG_contDiffOn hg hU hz hyy).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 1

theorem heightOriginalC0_eq (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) (ell : ℕ) :
    heightOriginalC0 g z ell p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * curvatureDriftError g z p +
        (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * coordPartial 1 (darbouxG g z) p) := by
  unfold heightOriginalC0
  rw [geometric_quotient_drift hg hU hz hD hp (hyy p hp), heightOriginalA_partial_y hg hU hz hyy hp]

theorem heightChartA_eq (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) :
    heightChartA g z Y p = heightChartG1 g z Y p * capPullback Y (gaussianCurvature g) p := by
  unfold heightChartA heightChartG1 capTransportA capPullback heightOriginalA
  ring

theorem heightChartG1_pos (g : MetricField) (z : Coord → ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) (hE : 0 < heightEnergy g z (capChart Y p))
    (hyy : covHessian g z (capChart Y p) 1 1 ≠ 0) :
    0 < heightChartG1 g z Y p :=
  mul_pos (darbouxG_pos g z (capChart Y p) hE hyy) (pow_pos (capChartRho_pos hY hvar hp) _)

theorem heightChartA_partial_initial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (heightChartA g z Y) p =
      darbouxG g z (capChart Y p) * capChartRho Y p * coordPartial 1 (gaussianCurvature g) (capChart Y p) +
        gaussianCurvature g (capChart Y p) *
          (capChartRho Y p * coordPartial 1 (darbouxG g z) (capChart Y p) +
            2 * darbouxG g z (capChart Y p) * capChartSigma Y p) := by
  rw [heightChartA, capTransportA_partial_initial hY hvar
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hmap hp]
  unfold capPullback
  rw [heightOriginalA_partial_y hg hU hz hyy (hmap hp)]
  unfold heightOriginalA
  ring

theorem heightChartC_expanded
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p =
      gaussianCurvature g (capChart Y p) * darbouxG g z (capChart Y p) * capChartSigma Y p +
        capChartRho Y p *
          (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
            gaussianCurvature g (capChart Y p) * curvatureDriftError g z (capChart Y p) +
            (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
              gaussianCurvature g (capChart Y p) * coordPartial 1 (darbouxG g z) (capChart Y p))) := by
  unfold heightChartC capTransportC capPullback heightOriginalA
  rw [heightOriginalC0_eq hg hU hz hD hyy (hmap hp) ell]
  ring

theorem heightChartC_factor
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
      heightChartA g z Y p * heightChartRemainder g z Y ell p := by
  have hGne := (darbouxG_pos g z (capChart Y p) (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
  have hrhone := (capChartRho_pos hY hvar hp).ne'
  rw [heightChartC_expanded hg hU hz hD hyy hmap hp ell,
    heightChartA_partial_initial hg hU hz hyy hY hvar hmap hp]
  unfold heightChartA capTransportA heightOriginalA heightChartRemainder capPullback
  rw [SmoothLocal.DriftAlgebra.transverse_coefficient_polynomial,
    SmoothLocal.DriftAlgebra.transverse_coefficient_factor _ _ _ _ _ _ _ hGne hrhone]

theorem heightChartA_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (heightChartA g z Y) capChartDomain :=
  (capPullback_contDiffOn hY (heightOriginalA_contDiffOn hg hU hz hyy) hmap).mul
    ((capChartRho_contDiffOn hY hvar).pow 2)

theorem heightChartRemainder_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain := by
  have hG := darbouxG_contDiffOn hg hU hz hyy
  have hPG := capPullback_contDiffOn hY hG hmap
  have hPGy := capPullback_contDiffOn hY (partial_contDiffOn hG hU 1) hmap
  have hPR := capPullback_contDiffOn hY (curvatureDriftError_contDiffOn hg hU hz hyy) hmap
  have hrho := capChartRho_contDiffOn hY hvar
  have hsigma := capChartSigma_contDiffOn hY hvar
  exact ((hPR.sub hPGy).div (hPG.mul hrho) (fun _ hp =>
    mul_ne_zero (darbouxG_pos g z _ (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
      (capChartRho_pos hY hvar hp).ne')).sub
    ((contDiffOn_const.mul hsigma).div (hrho.pow 2)
      (fun _ hp => pow_ne_zero 2 (capChartRho_pos hY hvar hp).ne'))

theorem heightChartC_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartC g z Y ell) capChartDomain := by
  have hA := heightChartA_contDiffOn hg hU hz hyy hY hvar hmap
  have hr := heightChartRemainder_contDiffOn hg hU hz hyy hE hY hvar hmap ell
  exact ((contDiffOn_const.mul (partial_contDiffOn hA capChartDomain_isOpen 1)).add (hA.mul hr)).congr
    (fun _ hp => heightChartC_factor hg hU hz hD hyy hE hY hvar hmap hp ell)

theorem heightChartRemainder_bounded_on_compact {Q : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ)
    (hQ : IsCompact Q) (hQU : Q ⊆ capChartDomain) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Q, |heightChartRemainder g z Y ell p| ≤ B := by
  have hc : ContinuousOn (heightChartRemainder g z Y ell) Q :=
    (heightChartRemainder_contDiffOn hg hU hz hyy hE hY hvar hmap ell).continuousOn.mono hQU
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp
  have hb : |heightChartRemainder g z Y ell p| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB p hp
  exact hb.trans (le_max_left _ _)

theorem height_coefficient_operator_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-(hessianQuotient g z) (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ capChartDomain) (ell : ℕ) :
    capPullback Y (driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z ell) (heightOriginalC0 g z ell) u) p =
      multiplierOperator (heightChartA g z Y) (heightChartB g z Y ell)
        (heightChartC g z Y ell) (capPullback Y u) p :=
  cap_driftOperator_transport _ _ _ hY hode hvar (hessianQuotient_contDiffOn hg hU hz hyy)
    hu hU hmap hp

end SmoothLocal.Flow

end

end OAI
