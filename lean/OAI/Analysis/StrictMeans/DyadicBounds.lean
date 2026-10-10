import OAI.Analysis.StrictMeans.TransferOperator

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma cayleyToDisk_norm_relation (z : UpperHalfPlane) :
    (1 - ‖cayleyToDisk z‖ ^ 2) * ‖(z : ℂ) + I‖ ^ 2 = 4 * z.im := by
  have hd : ‖(z : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr (add_I_ne_zero z.im_pos)
  rw [cayleyToDisk, norm_div, div_pow]
  field_simp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, add_re, I_re, add_zero, add_im, I_im,
    sub_re, sub_zero, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

lemma halfPlaneQ_norm (f : DiskFamily) (z : UpperHalfPlane) :
    ‖halfPlaneQ f z‖ = ‖(z : ℂ) + I‖ ^ 2 /
      (4 * ‖deriv (diskExtension f.val) (cayleyToDisk z)‖) := by
  rw [halfPlaneQ, norm_inv, halfPlaneFunction_deriv f z.im_pos]
  simp only [norm_mul, norm_ofNat, norm_I, mul_one, norm_div, norm_pow]
  field_simp
  ring

lemma halfPlaneQ_strip_bound (f : DiskFamily) (z : UpperHalfPlane)
    (hx : |z.re| ≤ 2) (hy : z.im ≤ 1) : ‖halfPlaneQ f z‖ ≤ 64 / z.im := by
  let r := ‖cayleyToDisk z‖
  let d := ‖deriv (diskExtension f.val) (cayleyToDisk z)‖
  let D := ‖(z : ℂ) + I‖ ^ 2
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr : r < 1 := by
    simpa only [mem_ball, dist_zero_right] using cayleyToDisk_mem z.im_pos
  have hD0 : 0 ≤ D := sq_nonneg _
  have hD : D ≤ 8 := by
    dsimp only [D]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, add_re, add_im, I_re, I_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have ha := abs_le.mp hx
    nlinarith [z.im_pos]
  have hd0 : 0 < d := norm_pos_iff.mpr
    (diskFamily_derivative_ne_zero f ⟨_, cayleyToDisk_mem z.im_pos⟩)
  have hrel : (1 - r) * (1 + r) * D = 4 * z.im := by
    have hh := cayleyToDisk_norm_relation z
    dsimp only [r, D]
    nlinarith [hh]
  have hylo : z.im ≤ 4 * (1 - r) := by
    have h := mul_le_mul_of_nonneg_left hD (mul_nonneg (by linarith) (by linarith))
    have h' := mul_le_mul_of_nonneg_left (show 1 + r ≤ 2 by linarith)
      (show 0 ≤ 8 * (1 - r) by positivity)
    nlinarith
  have hd := (derivative_distortion f.property.1 f.property.2.1 f.property.2.2.2 hr).1
  change (1 - r) / (1 + r) ^ 3 ≤ d at hd
  have hp : 0 < (1 + r) ^ 3 := pow_pos (by linarith) _
  have hd' := (div_le_iff₀ hp).mp hd
  have hc : (1 + r) ^ 3 ≤ 8 := by
    simpa only [show (2 : ℝ)^3 = 8 by norm_num] using pow_le_pow_left₀ (show 0 ≤ 1 + r by linarith)
      (show 1 + r ≤ 2 by linarith) 3
  have hds : z.im ≤ 32 * d := by
    have hh := mul_le_mul_of_nonneg_left hc hd0.le
    nlinarith
  rw [halfPlaneQ_norm, div_le_div_iff₀ (mul_pos (by norm_num) hd0) z.im_pos]
  change D * z.im ≤ 64 * (4 * d)
  have hh := mul_le_mul_of_nonneg_right hD z.im_pos.le
  nlinarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

def xyPoint (x y : ℝ) (hy : 0 < y) : UpperHalfPlane := ⟨x + y * I, by simpa⟩
@[simp] lemma xyPoint_re (x y : ℝ) (hy : 0 < y) : (xyPoint x y hy).re = x := by simp [xyPoint]
@[simp] lemma xyPoint_im (x y : ℝ) (hy : 0 < y) : (xyPoint x y hy).im = y := by simp [xyPoint]

lemma affineProduct_xyPoint (x y s t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    affineProduct (xyPoint x y hy) (xyPoint s t ht) =
      xyPoint (x + y * s) (y * t) (mul_pos hy ht) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, xyPoint]
  ring

def horizontalPoint (x : ℝ) : UpperHalfPlane := xyPoint x 1 zero_lt_one

def dyadicHeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
lemma dyadicHeight_pos (n : ℕ) : 0 < dyadicHeight n := pow_pos (by norm_num) _
lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)
lemma dyadicHeight_succ (n : ℕ) : dyadicHeight (n + 1) = dyadicHeight n / 2 := by
  simp [dyadicHeight, pow_succ, div_eq_mul_inv]

def gridStart (n : ℕ) : UpperHalfPlane :=
  xyPoint (-1 + dyadicHeight n) (dyadicHeight n) (dyadicHeight_pos n)
def gridEnd (n : ℕ) : UpperHalfPlane :=
  xyPoint (1 + dyadicHeight n) (dyadicHeight n) (dyadicHeight_pos n)

lemma dyadicLeft_gridStart (n : ℕ) : affineProduct dyadicLeft (gridStart n) = gridStart (n + 1) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, gridStart, xyPoint, dyadicHeight_succ]
  ring
lemma dyadicRight_gridEnd (n : ℕ) : affineProduct dyadicRight (gridEnd n) = gridEnd (n + 1) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, gridEnd, xyPoint, dyadicHeight_succ]
  ring
lemma dyadic_gridMiddle (n : ℕ) :
    affineProduct dyadicLeft (gridEnd n) = affineProduct dyadicRight (gridStart n) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, dyadicRight, gridStart, gridEnd, xyPoint]
  ring

lemma dyadic_shift (n : ℕ) :
    dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n =
      dyadicHeight n • (affineOperator (gridEnd n) - affineOperator (gridStart n)) := by
  induction n with
  | zero =>
    have hs : gridStart 0 = UpperHalfPlane.I := by apply UpperHalfPlane.ext; simp [gridStart, dyadicHeight, xyPoint]
    have he : gridEnd 0 = horizontalPoint 2 := by apply UpperHalfPlane.ext; norm_num [gridEnd, horizontalPoint, dyadicHeight, xyPoint]
    simp [hs, he, dyadicHeight]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← mul_sub, ih, mul_smul_comm,
      dyadicOperator, smul_mul_assoc, smul_smul, mul_sub, add_mul, add_mul,
      affineOperator_mul, affineOperator_mul, affineOperator_mul, affineOperator_mul,
      dyadicLeft_gridStart, dyadicRight_gridEnd, dyadic_gridMiddle]
    have hc (a b c : C(DiskFamily, ℝ) →L[ℝ] C(DiskFamily, ℝ)) :
        (c + a) - (b + c) = a - b := by abel
    rw [hc]
    congr 1

lemma affineOperator_norm_bound {z : UpperHalfPlane} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : DiskFamily, ‖halfPlaneQ f z‖ ≤ C) : ‖affineOperator z‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro φ
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).mpr
  intro f
  rw [affineOperator_apply, norm_mul, norm_norm]
  exact mul_le_mul (h f) (φ.norm_coe_le_norm _) (norm_nonneg _) hC

lemma affineOperator_strip_norm (z : UpperHalfPlane) (hx : |z.re| ≤ 2) (hy : z.im ≤ 1) :
    ‖affineOperator z‖ ≤ 64 / z.im :=
  affineOperator_norm_bound (by positivity) (fun f => halfPlaneQ_strip_bound f z hx hy)

lemma dyadic_shift_norm_le (n : ℕ) :
    ‖dyadicOperator ^ n * affineOperator (horizontalPoint 2) - dyadicOperator ^ n‖ ≤ 128 := by
  have hv := dyadicHeight_pos n
  have hv1 := dyadicHeight_le_one n
  have hs := affineOperator_strip_norm (gridStart n)
    (by simp only [gridStart, xyPoint_re]; rw [abs_le]; constructor <;> linarith)
    (by simpa only [gridStart, xyPoint_im] using hv1)
  have he := affineOperator_strip_norm (gridEnd n)
    (by simp only [gridEnd, xyPoint_re]; rw [abs_le]; constructor <;> linarith)
    (by simpa only [gridEnd, xyPoint_im] using hv1)
  simp only [gridEnd, gridStart, xyPoint_im] at hs he
  rw [dyadic_shift]
  calc
    _ ≤ ‖dyadicHeight n‖ * ‖affineOperator (gridEnd n) - affineOperator (gridStart n)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ dyadicHeight n * (‖affineOperator (gridEnd n)‖ + ‖affineOperator (gridStart n)‖) := by
      rw [Real.norm_of_nonneg hv.le]
      apply mul_le_mul_of_nonneg_left _ hv.le
      exact norm_sub_le (affineOperator (gridEnd n)) (affineOperator (gridStart n))
    _ ≤ dyadicHeight n * (64 / dyadicHeight n + 64 / dyadicHeight n) :=
      mul_le_mul_of_nonneg_left (add_le_add he hs) hv.le
    _ = 128 := by field_simp; ring

end
end StrictInverseFirstPower

end

end OAI
