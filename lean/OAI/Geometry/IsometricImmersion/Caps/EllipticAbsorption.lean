import OAI.Geometry.IsometricImmersion.Caps.EllipticEnergy
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem weighted_young (w x y : ℝ) (hw : 0 < w) :
    |x * y| ≤ (w * x ^ 2 + y ^ 2 / w) / 2 := by
  have hminus : 0 ≤ w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x - y)) hw.le
    have he : (w * x - y) ^ 2 / w = w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  have hplus : 0 ≤ w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x + y)) hw.le
    have he : (w * x + y) ^ 2 / w = w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  apply abs_le.mpr
  constructor <;> nlinarith

theorem elliptic_error_scalar_bound
    (A v u x y eT eS H : ℝ) (hv : 0 < v) (hA : 0 < A)
    (hratio : eT ^ 2 / v + eS ^ 2 / (A * v) ≤ H) :
    |u * (eT * x + eS * y)| ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
  have hx := weighted_young v x (u * eT) hv
  have hy := weighted_young (A * v) y (u * eS) (mul_pos hA hv)
  calc
    |u * (eT * x + eS * y)| = |x * (u * eT) + y * (u * eS)| := by congr 1; ring
    _ ≤ |x * (u * eT)| + |y * (u * eS)| := abs_add_le _ _
    _ ≤ (v * x ^ 2 + (u * eT) ^ 2 / v) / 2 +
        (A * v * y ^ 2 + (u * eS) ^ 2 / (A * v)) / 2 := add_le_add hx hy
    _ = v * (x ^ 2 + A * y ^ 2) / 2 +
        (eT ^ 2 / v + eS ^ 2 / (A * v)) * u ^ 2 / 2 := by
      field_simp [ne_of_gt hv, ne_of_gt hA]
      ring
    _ ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg u)]

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticErrors_zero_of_nonneg
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q) (hzero : v p = 0) :
    ellipticErrorT B v p = 0 ∧ ellipticErrorS A C v p = 0 := by
  have hmin : IsLocalMin v p := by
    change ∀ᶠ q in 𝓝 p, v p ≤ v q
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [hzero] using hvn q hq
  have hdv := hmin.fderiv_eq_zero
  have hpv (i : Fin 2) : coordPartial i v p = 0 := by simp [coordPartial, hdv]
  constructor
  · simp [ellipticErrorT, hpv 0, hzero]
  · rw [ellipticErrorS, HessianCalculus.coordPartial_mul_at hA hv 1]
    simp [hpv 1, hzero]

theorem ellipticError_abs_bound
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q)
    (H : ℝ) (hH : 0 ≤ H)
    (hpos : 0 < v p → 0 < A p)
    (hratio : 0 < v p → (ellipticErrorT B v p) ^ 2 / v p +
      (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    |ellipticError A B C v u p| ≤ ellipticEnergy A v u p / 2 + H * (u p) ^ 2 / 2 := by
  by_cases hzero : v p = 0
  · have hz := ellipticErrors_zero_of_nonneg (B := B) (C := C) hU hp hA hv hvn hzero
    simp only [ellipticError, ellipticEnergy, hz.1, hz.2, hzero,
      zero_mul, add_zero, mul_zero, abs_zero, zero_div, zero_add]
    exact div_nonneg (mul_nonneg hH (sq_nonneg _)) (by norm_num)
  · have hvpos : 0 < v p := lt_of_le_of_ne (hvn p hp) (Ne.symm hzero)
    exact elliptic_error_scalar_bound (A p) (v p) (u p)
      (coordPartial 0 u p) (coordPartial 1 u p)
      (ellipticErrorT B v p) (ellipticErrorS A C v p) H hvpos (hpos hvpos) (hratio hvpos)

theorem ellipticEnergy_nonneg (A v u : Coord → ℝ) (p : Coord)
    (hv : 0 ≤ v p) (hA : 0 < v p → 0 < A p) : 0 ≤ ellipticEnergy A v u p := by
  by_cases hz : v p = 0
  · simp [ellipticEnergy, hz]
  · have hvpos : 0 < v p := lt_of_le_of_ne hv (Ne.symm hz)
    exact mul_nonneg hv (add_nonneg (sq_nonneg _) (mul_nonneg (hA hvpos).le (sq_nonneg _)))

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_sub {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => F p - G p) =
      rectangleIntegral tl tr sb st F - rectangleIntegral tl tr sb st G := by
  simp only [sub_eq_add_neg]
  have hneg : ContinuousOn (fun p => -G p) (closedRectangle tl tr sb st) := hG.neg
  rw [rectangleIntegral_add ht hs hF hneg, rectangleIntegral_neg]

theorem rectangleIntegral_mono {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ closedRectangle tl tr sb st, F p ≤ G p) :
    rectangleIntegral tl tr sb st F ≤ rectangleIntegral tl tr sb st G := by
  rw [rectangleIntegral_eq_area ht hs hF, rectangleIntegral_eq_area ht hs hG]
  apply setIntegral_mono_on (rectangle_area_integrable hF) (rectangle_area_integrable hG)
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact hle (boxPoint p.1 p.2) (boxPoint_mem
    (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2))

theorem integrated_elliptic_energy_bound
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ ∞ v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (V H : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hvn : ∀ p ∈ U, 0 ≤ v p)
    (hvV : ∀ p ∈ closedRectangle tl tr sb st, v p ≤ V)
    (hpos : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p → 0 < A p)
    (hratio : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p →
      (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) ≤
      V * rectangleIntegral tl tr sb st (fun p => (f p) ^ 2) +
        (V + H) * rectangleIntegral tl tr sb st (fun p => (u p) ^ 2) := by
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  obtain ⟨_, _, hE, hErr⟩ := elliptic_fields_contDiffOn hU hA hB hC hv hu
  have hSource := (hv.mul hu).mul hf
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      -(v p * u p * f p) - ellipticError A B C v u p ≤
        (1 / 2 : ℝ) * ellipticEnergy A v u p +
          ((V + H) / 2) * (u p) ^ 2 + (V / 2) * (f p) ^ 2 := by
    have hpU := hbox hp
    have hErrBound := ellipticError_abs_bound (u := u) hU hpU
      ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      ((hv.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      hvn H hH (hpos p hp) (hratio p hp)
    have hyoung : -(u p * f p) ≤ ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [sq_nonneg (u p + f p)]
    have hm := mul_le_mul_of_nonneg_left hyoung (hvn p hpU)
    have hcost := mul_le_mul (hvV p hp) (le_refl (((u p) ^ 2 + (f p) ^ 2) / 2))
      (div_nonneg (add_nonneg (sq_nonneg (u p)) (sq_nonneg (f p)))
        (by norm_num : (0 : ℝ) ≤ 2)) hV
    have hsource : -(v p * u p * f p) ≤ V * ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [hm, hcost]
    nlinarith [hsource, neg_le_abs (ellipticError A B C v u p)]
  have hEhalf : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p)
      (closedRectangle tl tr sb st) := (contDiffOn_const.mul hE).continuousOn.mono hbox
  have hUhalf : ContinuousOn (fun p => ((V + H) / 2) * (u p) ^ 2)
      (closedRectangle tl tr sb st) := (contDiffOn_const.mul (hu.pow 2)).continuousOn.mono hbox
  have hFhalf : ContinuousOn (fun p => (V / 2) * (f p) ^ 2)
      (closedRectangle tl tr sb st) := (contDiffOn_const.mul (hf.pow 2)).continuousOn.mono hbox
  have hi := rectangleIntegral_mono ht hs
    ((hSource.neg.sub hErr).continuousOn.mono hbox) ((hEhalf.add hUhalf).add hFhalf) hpoint
  simp only [Pi.add_def] at hi
  have hsum : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p +
      ((V + H) / 2) * (u p) ^ 2) (closedRectangle tl tr sb st) := hEhalf.add hUhalf
  have heq := integrated_elliptic_equation ht hs hU hA hB hC hv hu hbox hboundary hEq
  have hleft : rectangleIntegral tl tr sb st
      (fun p => -(v p * u p * f p) - ellipticError A B C v u p) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) := by
    rw [rectangleIntegral_sub ht hs (hSource.neg.continuousOn.mono hbox)
      (hErr.continuousOn.mono hbox), rectangleIntegral_neg]
    exact heq.symm
  rw [hleft,
    rectangleIntegral_add ht hs hsum hFhalf,
    rectangleIntegral_add ht hs hEhalf hUhalf,
    rectangleIntegral_const_mul tl tr sb st (1 / 2 : ℝ) (ellipticEnergy A v u),
    rectangleIntegral_const_mul tl tr sb st ((V + H) / 2) (fun p => (u p) ^ 2),
    rectangleIntegral_const_mul tl tr sb st (V / 2) (fun p => (f p) ^ 2)] at hi
  nlinarith

end SmoothLocal.Weighted

end

end OAI
