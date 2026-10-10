import OAI.Geometry.IsometricImmersion.Caps.EllipticC1
import OAI.Geometry.IsometricImmersion.Caps.EllipticRatio
import OAI.Geometry.IsometricImmersion.Caps.EllipticCutoffEdge

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def threeEdgeDerivativeConstant (l0 l1 r1 r0 a0 a1 : ℝ) : ℝ :=
  transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) +
    transitionDerivativeBound / (a1 - a0)

theorem threeEdgeDerivativeConstant_nonneg {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) :
    0 ≤ threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have ht := transitionDerivativeBound_pos.le
  have hl := sub_pos.mpr hL
  have hr := sub_pos.mpr hR
  have hs := sub_pos.mpr hS
  unfold threeEdgeDerivativeConstant
  positivity

theorem threeEdgeCutoff_partial_common {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) (i : Fin 2) :
    |coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
      threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have hb := threeEdgeCutoff_partial_bounds hL hR hS p
  have ht := transitionDerivativeBound_pos.le
  have hl : 0 ≤ transitionDerivativeBound / (l1 - l0) := div_nonneg ht (sub_pos.mpr hL).le
  have hr : 0 ≤ transitionDerivativeBound / (r0 - r1) := div_nonneg ht (sub_pos.mpr hR).le
  have hs : 0 ≤ transitionDerivativeBound / (a1 - a0) := div_nonneg ht (sub_pos.mpr hS).le
  unfold threeEdgeDerivativeConstant
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;> linarith [hb.1, hb.2]

theorem ellipticWeightC1_errors_eq {b c : ℝ} (A B C chi K : Coord → ℝ)
    {p : Coord} (hp : p 1 < b) :
    ellipticErrorT B (ellipticWeightC1 b c chi K) p =
        ellipticErrorT B (ellipticWeight b c chi K) p ∧
      ellipticErrorS A C (ellipticWeightC1 b c chi K) p =
        ellipticErrorS A C (ellipticWeight b c chi K) p := by
  have he : (fun q => A q * ellipticWeightC1 b c chi K q) =ᶠ[𝓝 p]
      (fun q => A q * ellipticWeight b c chi K q) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    rw [ellipticWeightC1_eq hq.le]
  have hderiv : coordPartial 1 (fun q => A q * ellipticWeightC1 b c chi K q) p =
      coordPartial 1 (fun q => A q * ellipticWeight b c chi K q) p := by
    unfold coordPartial
    rw [he.fderiv_eq]
  constructor
  · rw [ellipticErrorT, ellipticErrorT, ellipticWeightC1_partial_eq hp 0,
      ellipticWeightC1_eq hp.le]
  · rw [ellipticErrorS, ellipticErrorS, hderiv, ellipticWeightC1_eq hp.le]

theorem threeEdge_ellipticWeight_boundary {l0 l1 r1 r0 a0 a1 b c : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (K : Coord → ℝ) :
    zeroRectangleBoundary l0 r0 a0 b
      (ellipticWeightC1 b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) := by
  constructor
  · intro s hs
    have hl := threeEdgeCutoff_zero hL hR hS (boxPoint l0 s)
      (Or.inl (by simp [boxPoint]))
    have hr := threeEdgeCutoff_zero hL hR hS (boxPoint r0 s)
      (Or.inr (Or.inl (by simp [boxPoint])))
    constructor <;> simp [ellipticWeightC1, hl, hr]
  · intro t ht
    have hb := threeEdgeCutoff_zero hL hR hS (boxPoint t a0)
      (Or.inr (Or.inr (by simp [boxPoint])))
    constructor
    · simp [ellipticWeightC1, hb]
    · exact ellipticWeightC1_zero (by simp [boxPoint])

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c MK g0 M : ℝ}

theorem threeEdge_elliptic_energy_bound
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1)
    (ht : l0 ≤ r0) (hs : a0 ≤ b) (hc : 0 < c)
    (hMK : 0 ≤ MK) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U) (hG1 : ContDiffOn ℝ ∞ G1 U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle l0 r0 a0 b ⊆ U)
    (hEq : ∀ p ∈ U, multiplierOperator (fun q => G1 q * K q) B C u p = f p)
    (hKi : ∀ p ∈ closedRectangle l0 r0 a0 b, ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hGlow : ∀ p ∈ closedRectangle l0 r0 a0 b, g0 ≤ G1 p)
    (hAhi : ∀ p ∈ closedRectangle l0 r0 a0 b, |G1 p * K p| ≤ M)
    (hAs : ∀ p ∈ closedRectangle l0 r0 a0 b,
      |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hBb : ∀ p ∈ closedRectangle l0 r0 a0 b, |B p| ≤ M)
    (hCb : ∀ p ∈ closedRectangle l0 r0 a0 b, |C p| ≤ M) :
    rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeight b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) u) ≤
      (b - a0) ^ 6 * rectangleIntegral l0 r0 a0 b (fun p => (f p) ^ 2) +
        ((b - a0) ^ 6 + ellipticRatioConstant (b - a0) (g0 * c / 2)
          (ellipticCutoffDerivativeConstant c MK (threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1)) M) *
          rectangleIntegral l0 r0 a0 b (fun p => (u p) ^ 2) := by
  let chi := threeEdgeCutoff l0 l1 r1 r0 a0 a1
  let v := ellipticWeightC1 b c chi K
  let X := threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1
  let H := ellipticRatioConstant (b - a0) (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M
  have hX : 0 ≤ X := threeEdgeDerivativeConstant_nonneg hL hR hS
  have hchi : ContDiffOn ℝ ∞ chi U := (threeEdgeCutoff_contDiff _ _ _ _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v U := ellipticWeightC1_contDiffOn hc
    (hchi.of_le (by simp)) (hK.of_le (by simp))
  have hA : ContDiffOn ℝ ∞ (fun q => G1 q * K q) U := hG1.mul hK
  have hH : 0 ≤ H := ellipticRatioConstant_nonneg (sub_nonneg.mpr hs) (by positivity) hM
  have hposD (p : Coord) (hpv : 0 < v p) : p 1 < b := by
    by_contra hn
    have hz : v p = 0 := ellipticWeightC1_zero (le_of_not_gt hn)
    linarith
  have hweightEq (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) :
      v p = ellipticWeight b c chi K p := ellipticWeightC1_eq hp.2.2
  have hposA (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      0 < G1 p * K p := by
    have hd := hposD p hpv
    have hcurv := ellipticWeight_pos_implies_curvature hc hd
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
    have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c / 2) (sub_pos.mpr hd)).trans hcurv
    exact mul_pos (hg0.trans_le (hGlow p hp)) hKpos
  have hratio (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      (ellipticErrorT B v p) ^ 2 / v p +
        (ellipticErrorS (fun q => G1 q * K q) C v p) ^ 2 / (G1 p * K p * v p) ≤ H := by
    have hd := hposD p hpv
    have herrors := ellipticWeightC1_errors_eq (c := c) (fun q => G1 q * K q) B C chi K hd
    change (ellipticErrorT B (ellipticWeightC1 b c chi K) p) ^ 2 / v p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeightC1 b c chi K) p) ^ 2 /
        (G1 p * K p * v p) ≤ H
    rw [herrors.1, herrors.2, hweightEq p hp]
    exact ellipticCutoff_actual_ratio hc (sub_pos.mpr hd)
      (by unfold edgeDistance; linarith [hp.2.1]) hMK hX hg0 hM
      ((hchi.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      ((hK.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      ((hG1.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      (threeEdgeCutoff_range _ _ _ _ _ _ p)
      (threeEdgeCutoff_partial_common hL hR hS p) (hKi p hp)
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
      (hGlow p hp) (hAhi p hp) (hAs p hp) (hBb p hp) (hCb p hp)
  have hestimate := integrated_elliptic_energy_bound_C1 ht hs hU hA hB hC hv hu hbox
    (threeEdge_ellipticWeight_boundary hL hR hS K) hEq ((b - a0) ^ 6) H
    (by positivity) hH (fun p _ => ellipticWeightC1_nonneg _ _ _ _ p)
    (fun p hp => (ellipticWeightC1_le_distance_six _ _ _ _ p
      (threeEdgeCutoff_range _ _ _ _ _ _ p)).trans
        (pow_le_pow_left₀ (sub_nonneg.mpr hp.2.2)
          (by linarith [hp.2.1]) 6))
    hposA hratio
  have henergyEq : rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q) v u) =
      rectangleIntegral l0 r0 a0 b
        (ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u) := by
    apply rectangleIntegral_congr ht hs
    intro p hp
    change v p * _ = ellipticWeight b c chi K p * _
    rw [hweightEq p hp]
  rw [henergyEq] at hestimate
  exact hestimate

end SmoothLocal.Weighted

end

end OAI
