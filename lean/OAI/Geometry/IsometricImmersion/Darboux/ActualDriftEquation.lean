import OAI.Geometry.IsometricImmersion.Calculus.HessianTransport
import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftCoefficients
import OAI.Geometry.IsometricImmersion.Darboux.DriftTransportAlgebra
import OAI.Geometry.IsometricImmersion.Darboux.DarbouxJet

namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem hessian_quotient_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * christoffelAlongD g p (hessianQuotient g z p) 0 -
      christoffelAlongD g p (hessianQuotient g z p) 1 =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p *
          (coordPartial 1 (heightEnergy g z) p / (covHessian g z p 1 1) ^ 2 -
            heightEnergy g z p * coordPartial 1 (fun q => covHessian g z q 1 1) p /
              (covHessian g z p 1 1) ^ 3 -
            darbouxG g z p * (christoffel g 0 0 1 p -
              hessianQuotient g z p * christoffel g 0 1 1 p) +
            driftJ g z p / covHessian g z p 1 1) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD p hp
  have hBx : coordPartial 0 (fun q => covHessian g z q 0 1) p -
      coordPartial 1 (fun q => covHessian g z q 0 0) p =
      -christoffel g 0 0 1 p * covHessian g z p 0 0 +
      (christoffel g 0 0 0 p - christoffel g 1 0 1 p) * covHessian g z p 0 1 +
      christoffel g 1 0 0 p * covHessian g z p 1 1 +
      gaussianCurvature g p * (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p) := by
    linear_combination -hessian_transport_Ay_Bx hg hU hz hp
  have hs := SmoothLocal.DriftAlgebra.quotient_transport_algebra
    (covHessian g z p 0 0) (covHessian g z p 0 1) (covHessian g z p 1 1)
    (coordPartial 1 (fun q => covHessian g z q 0 0) p)
    (coordPartial 0 (fun q => covHessian g z q 0 1) p)
    (coordPartial 1 (fun q => covHessian g z q 0 1) p)
    (coordPartial 0 (fun q => covHessian g z q 1 1) p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (gaussianCurvature g p) (coordPartial 1 (gaussianCurvature g) p)
    (heightEnergy g z p) (coordPartial 1 (heightEnergy g z) p)
    (christoffel g 0 0 0 p) (christoffel g 0 0 1 p) (christoffel g 0 1 1 p)
    (christoffel g 1 0 0 p) (christoffel g 1 0 1 p) (christoffel g 1 1 1 p)
    (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)
    (g p 0 1 * coordPartial 1 z p - g p 1 1 * coordPartial 0 z p)
    hyy hdet (darboux_determinant_derivative hg hU hz hD hp 1) hBx
    (hessian_transport_hx_By hg hU hz hp)
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hqD := coordinateDrift_self_quotient (hdH 0 1) (hdH 1 1) hyy
  change coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p = _ at hqD
  rw [hqD, christoffelAlongD_eq hg hU hp, christoffelAlongD_eq hg hU hp]
  dsimp only [hessianQuotient, darbouxG, driftJ]
  convert hs using 1
  ring

def heightPFirst (g : MetricField) (z : Coord → ℝ) (i : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (solvedDarboux g p
    (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p))
    (fun r => coordPartial r z p)

theorem heightPFirst_eq
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1) ^ 2) := by
  simpa only [heightPFirst, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z, hessianQuotient] using
    solvedDarboux_firstJet hg hU hp (fun r => coordPartial r z p)
      (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p) hyy i

theorem heightEnergy_jet_contraction (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    hessianQuotient g z p * coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) +
      coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) = -2 * driftJ g z p := by
  rw [coordPartial_jetEnergy, coordPartial_jetEnergy]
  norm_num
  rw [metric_coeff_symm hg hp 1 0]
  unfold driftJ
  ring

theorem geometric_quotient_drift
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * curvatureDriftError g z p := by
  have hd := hessian_quotient_transport hg hU hz hD hp hyy
  have he : coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 * driftJ g z p :=
    heightEnergy_y_quotient hg hU hz hp hyy
  have hr := SmoothLocal.DriftAlgebra.explicit_drift_remainder
    (covHessian g z p 1 1) (heightEnergy g z p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (hessianQuotient g z p)
    (christoffel g 0 0 1 p) (christoffel g 0 1 1 p) (christoffel g 1 1 1 p)
    (driftJ g z p)
    (coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (heightEnergy g z) p) hyy he (heightEnergy_jet_contraction hg hp)
  rw [heightPFirst_eq hg hU hp hyy 0, heightPFirst_eq hg hU hp hyy 1,
    curvatureDriftError_eq]
  dsimp only [darbouxG, connectionTraceY] at hd ⊢
  linear_combination hd + gaussianCurvature g p * hr

end SmoothLocal.Geometry

end

end OAI
