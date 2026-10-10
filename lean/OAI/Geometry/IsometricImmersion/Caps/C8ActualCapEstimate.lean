import OAI.Geometry.IsometricImmersion.Caps.UniformOriginalDataCapEstimate
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_actual_high_cap_estimate
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) (m : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
    let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
    let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
    let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
      (∀ p ∈ capChartDomain,
        multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
          (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
            capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
      ∀ L R bottom top b : ℝ,
        -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
        rectangleIntegral L R bottom top
          (fun p => (coordPartial 0 (capPullback Y (verticalJet z (m+3))) p)^2+
            (coordPartial 1 (capPullback Y (verticalJet z (m+3))) p)^2) ≤
          heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
            (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  have hg4 (i j : Fin 2) : CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G :=
    (coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)).mono (by norm_num) le_rfl
  have hz5 : CoordinateBound z modelSquare 5 Z := coordinateBound_five_of_frechet_eight hz hU hSU hzB
  exact exists_uniform_original_data_actual_high_cap_estimate hg hU hSU hz hG hZ hd hc he0 hg4 hz5
    hdet hyy hEfloor hsmall hD hk hbackground hsupport hcentral m

end SmoothLocal.Flow

end

end OAI
