import OAI.Geometry.IsometricImmersion.Energy.MovingEnergyGradient
import OAI.Geometry.IsometricImmersion.Energy.RectangleSobolevOne

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Sobolev

def spatialJet (f : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => f
  | n + 1 => coordPartial 0 (spatialJet f n)

theorem spatialJet_contDiffOn {f : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (spatialJet f n) U := by
  induction n with
  | zero => exact hf
  | succ n hn => exact partial_contDiffOn hn hU 0

theorem spatialJet_slice_hasDerivAt
    {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {x theta : ℝ} (hp : coordinatePoint x theta ∈ U) :
    HasDerivAt (fun xi => spatialJet f n (coordinatePoint xi theta))
      (spatialJet f (n + 1) (coordinatePoint x theta)) x := by
  have hd := ((spatialJet_contDiffOn hU hf n).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x theta)

theorem smooth_slice_memLp_two
    {f : Coord → ℝ} {U : Set Coord} {left right theta : ℝ}
    (hf : ContinuousOn f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => f (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) := by
  have hc : ContinuousOn (fun x => f (coordinatePoint x theta)) (Icc left right) :=
    hf.comp (by unfold coordinatePoint; fun_prop) hseg
  exact (memLp_two_iff_integrable_sq (hc.aestronglyMeasurable measurableSet_Icc)).2
    ((hc.pow 2).integrableOn_compact isCompact_Icc)

theorem interval_square_integral_le_of_eLpNorm
    {f : ℝ → ℝ} {left right : ℝ} {H : ℝ≥0} (hlr : left ≤ right)
    (hf : MemLp f 2 (volume.restrict (Icc left right)))
    (hH : eLpNorm f 2 (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)) :
    (∫ x in left..right, f x ^ 2) ≤ (H : ℝ) ^ 2 := by
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    integral_square_eq_L2_norm_square hf, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  have hh := ENNReal.toReal_mono (by simp : (H : ℝ≥0∞) ≠ ⊤) hH
  change (eLpNorm f 2 (volume.restrict (Icc left right))).toReal ≤ (H : ℝ) at hh
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).2 hh

theorem spatialJet_point_bound_from_same_interval_L2
    {f : Coord → ℝ} {U : Set Coord} {left right theta lengthFloor : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (n : ℕ) {H : ℝ≥0}
    (h0 : eLpNorm (fun x => spatialJet f n (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    (h1 : eLpNorm (fun x => spatialJet f (n + 1) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet f n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) := by
  have hlr : left < right := by linarith
  have hc0 : ContinuousOn (fun x => spatialJet f n (coordinatePoint x theta)) (Icc left right) :=
    (spatialJet_contDiffOn hU hf n).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hc1 : ContinuousOn (fun x => spatialJet f (n + 1) (coordinatePoint x theta))
      (Icc left right) :=
    (spatialJet_contDiffOn hU hf (n + 1)).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hp := interval_point_square_bound hlr hc0 hc1
    (fun x hx => spatialJet_slice_hasDerivAt hU hf n (hseg x hx)) hx
  have h0I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf n).continuousOn hseg) h0
  have h1I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf (n + 1)).continuousOn hseg) h1
  have hinv : 1 / (right - left) ≤ 1 / lengthFloor := by
    exact one_div_le_one_div_of_le hlength hwidth
  have hc : 0 ≤ 1 + 1 / (right - left) := by positivity
  have h0scale := mul_le_mul_of_nonneg_left h0I hc
  have hInvScale := mul_le_mul_of_nonneg_right hinv (sq_nonneg (H : ℝ))
  have hpoint : spatialJet f n (coordinatePoint x theta) ^ 2 ≤
      (2 + 1 / lengthFloor) * (H : ℝ) ^ 2 := by nlinarith
  have hpos : 0 ≤ 2 + 1 / lengthFloor := by positivity
  have hroot := Real.sq_sqrt hpos
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) H.2)).1
  rw [sq_abs, mul_pow, hroot]
  exact hpoint

def SpatialSliceL2Bound {ι : Type*} (F : ι → Coord → ℝ) (theta left right : ℝ)
    (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ i n, n ≤ N → eLpNorm (fun x => spatialJet (F i) n (coordinatePoint x theta)) 2
    (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)

theorem SpatialSliceL2Bound.pointwise_below_top
    {ι : Type*} {F : ι → Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor : ℝ} {N : ℕ} {H : ℝ≥0}
    (hL2 : SpatialSliceL2Bound F theta left right N H)
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (i : ι) (n : ℕ) (hn : n + 1 ≤ N) {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet (F i) n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) :=
  spatialJet_point_bound_from_same_interval_L2 hU (hF i) hseg hlength hwidth n
    (hL2 i n (by omega)) (hL2 i (n + 1) hn) hx

end SmoothLocal.Hyperbolic

end

end OAI
