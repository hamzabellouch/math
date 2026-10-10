import OAI.Geometry.IsometricImmersion.Caps.CapCutoffGeometry
import OAI.Geometry.IsometricImmersion.Caps.EllipticGradient
import OAI.Geometry.IsometricImmersion.Energy.DirectedEdgeDefect

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capOverlapThreshold (kappa c1 D : ℝ) : ℝ := min c1 (kappa / (D + 1))

theorem capOverlapThreshold_pos {kappa c1 D : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) :
    0 < capOverlapThreshold kappa c1 D := by
  exact lt_min hc1 (div_pos hk (by linarith))

theorem capOverlapThreshold_le (kappa c1 D : ℝ) :
    capOverlapThreshold kappa c1 D ≤ c1 := min_le_left _ _

theorem capOverlapThreshold_distance_le {kappa c1 D d : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (_ : 0 ≤ d) (hdD : d ≤ D) :
    capOverlapThreshold kappa c1 D * d ≤ kappa := by
  have hc := (capOverlapThreshold_pos hk hc1 hD).le
  have hD1 : 0 < D + 1 := by linarith
  have hcd : capOverlapThreshold kappa c1 D * (D + 1) ≤ kappa :=
    (le_div_iff₀ hD1).mp (min_le_right _ _)
  exact (mul_le_mul_of_nonneg_left (show d ≤ D + 1 by linarith) hc).trans hcd

theorem capOuterElliptic_gradient_pointwise
    {L R A b c g0 D : ℝ} {K G1 u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hc : 0 < c) (hg0 : 0 < g0) (hd : 0 < edgeDistance b p)
    (hdD : edgeDistance b p ≤ D) (hchi : capSpatialCutoff L R A p ≠ 0)
    (hK : c * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b c (capOuterSpatialCutoff L R A) K) u p := by
  have houter := capOuterSpatialCutoff_one_of_nonzero hL hR hA hchi
  have hh := ellipticCutoff_gradient_pointwise (u := u) hc le_rfl hg0 hd hdD houter hK hG1
  have hp : p 1 ≤ b := (sub_pos.mp hd).le
  simpa only [ellipticEnergy, ellipticWeightC1_eq hp] using hh

theorem directedCoercivityDefect_nonzero_cutoff
    {A B C chi I u : Coord → ℝ} {b lambda epsilon c2 : ℝ} {p : Coord}
    (hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≠ 0) : chi p ≠ 0 := by
  intro hz
  apply hdef
  simp only [directedCoercivityDefect, hz, zero_mul]

theorem capOuterElliptic_gradient_on_defect
    {L R A0 b c1 c2 kappa D g0 lambda epsilon : ℝ}
    {A B C K G1 I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : g0 ≤ G1 p)
    (hcoercive : K p ≤ c1 * edgeDistance b p →
      c2 * directedWeight b lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    (hdef : directedCoercivityDefect A B C (capSpatialCutoff L R A0) I u b lambda epsilon c2 p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (g0 * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A0) K) u p := by
  have hK : c1 * edgeDistance b p < K p := by
    by_contra h
    exact hdef (directedCoercivityDefect_zero _ _ _ _ _ _ _ _ _ _ _ (hcoercive (le_of_not_gt h)))
  apply capOuterElliptic_gradient_pointwise hL hR hA0 (capOverlapThreshold_pos hk hc1 hD)
    hg0 hd hdD (directedCoercivityDefect_nonzero_cutoff hdef) _ hG1
  exact (mul_le_mul_of_nonneg_right (capOverlapThreshold_le kappa c1 D) hd.le).trans hK.le

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem capOuterElliptic_gradient_on_actual_cutoff_support
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A b kappa c1 D glow : ℝ} {G1 u : Coord → ℝ} {p : Coord} {i : Fin 2}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hk : 0 < kappa)
    (hc1 : 0 < c1) (hD : 0 ≤ D) (hg : 0 < glow)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = SmoothLocal.Model.modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : glow ≤ G1 p)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (glow * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * capPullback Y (gaussianCurvature (g0 + eta)) q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A)
          (capPullback Y (gaussianCurvature (g0 + eta)))) u p := by
  have hK := capSpatialCutoff_partial_actual_curvature_lower hk hL hR hA hbackground hsupport
    hpU hdisp hpartial
  apply capOuterElliptic_gradient_pointwise hL hR hA (capOverlapThreshold_pos hk hc1 hD)
    hg hd hdD (capSpatialCutoff_nonzero_of_partial hpartial) _ hG1
  exact (capOverlapThreshold_distance_le hk hc1 hD hd.le hdD).trans hK.le

end SmoothLocal.Flow

end

end OAI
