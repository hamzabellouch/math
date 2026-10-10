import OAI.Geometry.IsometricImmersion.Taylor.TopChainExtraction
import OAI.Geometry.IsometricImmersion.Estimates.LargestBlockLinearization
import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientRegularity

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem second_fderiv_comp_constant_direction
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 1 J p, v] =
      coordPartial 1 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    convert fderiv_comp p hdF hJ using 1
    rfl
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem sixVariableP_second_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ r ∈ U, covHessian g z r 1 1 ≠ 0) (hp : p ∈ U)
    (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z p)
        ![coordPartial 1 (solutionJet z) p, v] =
      coordPartial 1 (heightPFirst g z 0) p * v 2 +
      coordPartial 1 (heightPFirst g z 1) p * v 3 +
      2 * coordPartial 1 (hessianQuotient g z) p * v 4 -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) p * v 5 := by
  rw [second_fderiv_comp_constant_direction
    (sixVariableP_contDiffAt_solutionJet hg hU hp (hyy _ hp))
    (((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))]
  have heq : (fun r => fderiv ℝ (sixVariableP g) (solutionJet z r) v) =ᶠ[𝓝 p]
      (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
        2 * hessianQuotient g z r * v 4 -
        ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) := by
    filter_upwards [hU.mem_nhds hp] with r hr
    exact sixVariableP_vertical_direction hg hU hr (hyy _ hr) v hv0 hv1
  have h0 := ((heightPFirst_contDiffOn hg hU hz hyy 0).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have h1 := ((heightPFirst_contDiffOn hg hU hz hyy 1).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hq := ((hessianQuotient_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hK := ((gaussianCurvature_contDiffOn hg hU).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hG := ((darbouxG_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have ha : DifferentiableAt ℝ (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) p := (hq.pow 2).add (hK.mul hG)
  have hd := (((h0.hasFDerivAt.mul_const (v 2)).add
    (h1.hasFDerivAt.mul_const (v 3))).add
    ((hq.hasFDerivAt.const_mul 2).mul_const (v 4))).sub (ha.hasFDerivAt.mul_const (v 5))
  simp only [Pi.add_def, Pi.sub_def] at hd
  unfold coordPartial
  rw [heq.fderiv_eq]
  change fderiv ℝ (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
      2 * hessianQuotient g z r * v 4 -
      ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) p
      (Pi.single 1 1) = _
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

def firstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 1 (heightPFirst g z 0) p * coordPartial 0 (verticalJet z n) p +
  coordPartial 1 (heightPFirst g z 1) p * coordPartial 1 (verticalJet z n) p

def secondJetCorrection (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  2 * coordPartial 1 (hessianQuotient g z) p * coordPartial 0 u p -
  coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
    gaussianCurvature g r * darbouxG g z r) p * coordPartial 1 u p

theorem actualP_pair_extract_secondJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.pair 1 n) y =
      secondJetCorrection g z (verticalJet z (n + 1)) ![x, y] +
        firstJetPairRemainder g z n ![x, y] := by
  have hfirst : iteratedDeriv 1 (solutionJetCurve z x) y =
      coordPartial 1 (solutionJet z) ![x, y] :=
    verticalJet_slice hU (solutionJet_contDiffOn hU hz) x 1 y hp
  rw [chainTerm_pair_eq, hfirst, solutionJetCurve_iteratedDeriv hU hz hp n hn]
  change iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_second_vertical_direction hg hU hz hyy hp _ (by rfl) (by rfl)]
  change
    coordPartial 1 (heightPFirst g z 0) ![x, y] * coordPartial 0 (verticalJet z n) ![x, y] +
    coordPartial 1 (heightPFirst g z 1) ![x, y] * coordPartial 1 (verticalJet z n) ![x, y] +
    2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
      coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
    coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) ![x, y] *
      coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y] = _
  unfold secondJetCorrection firstJetPairRemainder
  change _ =
    (2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) ![x, y] *
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]) + _
  ring

end SmoothLocal.HighEquation

end

end OAI
