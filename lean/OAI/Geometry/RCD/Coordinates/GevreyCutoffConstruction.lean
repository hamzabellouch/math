import OAI.Geometry.RCD.Coordinates.GevreyCompactBump
import OAI.Geometry.RCD.Coordinates.GevreyConvolution
import OAI.Geometry.RCD.Coordinates.EuclideanGevreyCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Construction of a Euclidean Gevrey cutoff

Convolve the normalized small Gevrey bump with the indicator of the
radius-5/2 ball. The resulting function is one on the radius-two ball,
vanishes outside radius three, and retains the order-two derivative
bound. This constructs the exact cutoff used in the chart iteration.
-/

open Set Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section
namespace RegularPointCoordinates

/-- The compact Gevrey input is constructed in every finite dimension. -/
theorem euclideanGevreyCutoffInput (n : ℕ) : EuclideanGevreyCutoffInput n := by
  classical
  obtain ⟨b, hb, hb0, hbpos, hbs, A, hA, hAb⟩ := exists_small_gevreyTwo_bump n
  have hbc : HasCompactSupport b := (isCompact_closedBall (0 : Euclidean n) (1 / 4)).of_isClosed_subset
    (isClosed_tsupport b) hbs
  have hbi : Integrable b volume := hb.continuous.integrable_of_hasCompactSupport hbc
  let I : ℝ := ∫ y, b y
  have hI : 0 < I := hb.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hbc hb0 hbpos.ne'
  let f : Euclidean n → ℝ := (closedBall 0 (5 / 2)).indicator (fun _ => 1)
  have hfi : Integrable f volume := (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (isCompact_closedBall (0 : Euclidean n) (5 / 2)).measure_ne_top)
  have hf0 (y : Euclidean n) : 0 ≤ f y := (indicator_nonneg fun _ _ => zero_le_one) y
  have hf1 (y : Euclidean n) : f y ≤ 1 := by
    by_cases hy : y ∈ closedBall (0 : Euclidean n) (5 / 2) <;> simp [f, hy]
  let L := ContinuousLinearMap.mul ℝ ℝ
  let h := f ⋆[L, volume] b
  have hh : ContDiff ℝ ∞ h := hbc.contDiff_convolution_right L hfi.locallyIntegrable hb
  have hleft (x : Euclidean n) : h x = ∫ y, b y * f (x - y) := by
    dsimp only [h]
    rw [← convolution_flip]
    simp [convolution_def, L]
  have hnonneg (x : Euclidean n) : 0 ≤ h x := by
    rw [hleft]
    exact integral_nonneg fun y => mul_nonneg (hb0 y) (hf0 _)
  have hle (x : Euclidean n) : h x ≤ I := by
    rw [hleft]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
      mul_nonneg (hb0 y) (hf0 _)) hbi
    filter_upwards with y
    simpa using mul_le_mul_of_nonneg_left (hf1 (x - y)) (hb0 y)
  have hcore (x : Euclidean n) (hx : ‖x‖ ≤ 2) : h x = I := by
    rw [hleft]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : b y = 0
    · simp [hy]
    have hy' : ‖y‖ ≤ (1 / 4 : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hbs (subset_closure hy)
    have hxy : x - y ∈ closedBall (0 : Euclidean n) (5 / 2) := by
      simp only [mem_closedBall, dist_zero_right]
      have := norm_sub_le x y
      linarith
    simp [f, hxy]
  have hzero (x : Euclidean n) (hx : x ∉ closedBall (0 : Euclidean n) 3) : h x = 0 := by
    rw [hleft]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    by_cases hy : b y = 0
    · simp [hy]
    have hy' : ‖y‖ ≤ (1 / 4 : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hbs (subset_closure hy)
    have hxy : x - y ∉ closedBall (0 : Euclidean n) (5 / 2) := by
      simp only [mem_closedBall, dist_zero_right] at hx ⊢
      have ht := norm_add_le (x - y) y
      rw [sub_add_cancel] at ht
      linarith
    simp [f, hxy]
  let J : ℝ := I⁻¹ * ‖L‖ * ∫ y, ‖f y‖
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hI.le) (norm_nonneg L))
      (integral_nonneg fun y => norm_nonneg (f y))
  let C : ℝ := A * max 1 J
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [le_max_left 1 J]
  let psi : Euclidean n → ℝ := fun x => I⁻¹ • h x
  refine ⟨{
    value := psi
    constant := C
    constant_ge_one := hC
    smooth := hh.const_smul I⁻¹
    nonneg := fun x => mul_nonneg (inv_nonneg.mpr hI.le) (hnonneg x)
    le_one := ?_
    core := ?_
    support := ?_
    jet := ?_ }⟩
  · intro x
    change I⁻¹ * h x ≤ 1
    calc
      _ ≤ I⁻¹ * I := mul_le_mul_of_nonneg_left (hle x) (inv_nonneg.mpr hI.le)
      _ = 1 := inv_mul_cancel₀ hI.ne'
  · intro x hx
    change I⁻¹ * h x = 1
    rw [hcore x hx, inv_mul_cancel₀ hI.ne']
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    exact hx (by simp [psi, hzero x hn])
  · intro m x
    have hj := norm_iteratedFDeriv_convolution_le m L hfi hb hbc
      (by positivity : 0 ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2) (hAb m) x
    have hp : J ≤ (max 1 J) ^ (m + 1) :=
      (le_max_right 1 J).trans (le_self_pow₀ (le_max_left 1 J) (by omega))
    calc
      ‖iteratedFDeriv ℝ m psi x‖ = I⁻¹ * ‖iteratedFDeriv ℝ m h x‖ := by
        rw [iteratedFDeriv_const_smul_apply' (hh.of_le (by simp)).contDiffAt,
          norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hI.le)]
      _ ≤ I⁻¹ * (‖L‖ * (A ^ (m + 1) * (m.factorial : ℝ) ^ 2) * ∫ y, ‖f y‖) :=
        mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr hI.le)
      _ = A ^ (m + 1) * (m.factorial : ℝ) ^ 2 * J := by dsimp [J]; ring
      _ ≤ A ^ (m + 1) * (m.factorial : ℝ) ^ 2 * (max 1 J) ^ (m + 1) := by
        gcongr
      _ = C ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by dsimp [C]; rw [mul_pow]; ring

end RegularPointCoordinates

end

end OAI
