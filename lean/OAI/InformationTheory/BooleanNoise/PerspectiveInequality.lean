import OAI.InformationTheory.BooleanNoise.LambdaScalars
import OAI.InformationTheory.BooleanNoise.PerspectiveJensen
import OAI.InformationTheory.BooleanNoise.PerspectiveLogTrapezoid
import OAI.InformationTheory.BooleanNoise.PerspectiveCalculus
import OAI.InformationTheory.BooleanNoise.CurvatureBounds
import OAI.InformationTheory.BooleanNoise.LRegularity
import OAI.InformationTheory.BooleanNoise.LShape
import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.CurvatureCertificates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def logBarrier (b : ℝ) : ℝ := -Real.log (1 - b)

@[simp] theorem logBarrier_zero : logBarrier 0 = 0 := by simp [logBarrier]

theorem hasDerivAt_logBarrier {b : ℝ} (hb : b < 1) :
    HasDerivAt logBarrier (1 / (1 - b)) b := by
  have h := (((hasDerivAt_const b (1 : ℝ)).sub (hasDerivAt_id b)).log
    (show 1 - b ≠ 0 by linarith)).neg
  convert! h using 1
  simp [neg_div]

theorem lambda_truncated_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k m : ℕ) :
    (1 - z ^ k) * lambda z ≤
      (∑ j ∈ Finset.range k, z ^ j / ((j : ℝ) + 1)) -
      ∑ j ∈ Finset.range m,
        (z ^ k * (z ^ j / ((j : ℝ) + 1)) -
          z ^ (j + k) / ((j : ℝ) + k + 1)) := by
  have hs := hasSum_lambda hz0 hz1
  have ht := (hasSum_nat_add_iff' k).mpr hs
  have hd := (hs.mul_left (z ^ k)).sub ht
  simp only [Nat.cast_add] at hd
  have hnonneg : ∀ j : ℕ,
      0 ≤ z ^ k * (z ^ j / ((j : ℝ) + 1)) -
        z ^ (j + k) / ((j : ℝ) + k + 1) := by
    intro j
    rw [sub_nonneg, ← mul_div_assoc, ← pow_add, Nat.add_comm k j]
    apply div_le_div_of_nonneg_left (pow_nonneg hz0 _) (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hp := sum_le_hasSum (Finset.range m) (fun j _ => hnonneg j) hd
  linarith

theorem lambda_cutoff_four {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda b ≤
      1 + b / 2 + b ^ 2 / 3 + b ^ 3 / 4 - (4 / 5 : ℝ) * b ^ 4 -
        b ^ 5 / 3 - (4 / 21 : ℝ) * b ^ 6 - b ^ 7 / 8 - (4 / 45 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper hb0 hb1 4 5
  norm_num [Finset.sum_range_succ] at h
  nlinarith

private theorem sq_lt_one_of_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) : b ^ 2 < 1 := by
  have h := mul_pos (sub_pos.mpr hb1) (show 0 < 1 + b by linarith)
  nlinarith

theorem lambda_cutoff_two_sq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda (b ^ 2) ≤
      1 + b ^ 2 / 2 - (2 / 3 : ℝ) * b ^ 4 - b ^ 6 / 4 - (2 / 15 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper (sq_nonneg b) (sq_lt_one_of_nonneg hb0 hb1) 2 3
  norm_num [Finset.sum_range_succ] at h
  nlinarith

def lambdaDerivativeFactor (b : ℝ) : ℝ :=
  9 - b - 3 * b ^ 2 - b ^ 3 - 3 * (1 - b ^ 4) * lambda b -
    2 * (1 - b ^ 4) * lambda (b ^ 2)

theorem lambda_polynomial_le_factor {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    4 - (5 / 2 : ℝ) * b - 5 * b ^ 2 - (7 / 4 : ℝ) * b ^ 3 +
      (56 / 15 : ℝ) * b ^ 4 + b ^ 5 + (15 / 14 : ℝ) * b ^ 6 +
      (3 / 8 : ℝ) * b ^ 7 + (8 / 15 : ℝ) * b ^ 8 ≤ lambdaDerivativeFactor b := by
  unfold lambdaDerivativeFactor
  have h1 := lambda_cutoff_four hb0 hb1
  have h2 := lambda_cutoff_two_sq hb0 hb1
  nlinarith

def lambdaAuxiliary (b : ℝ) : ℝ :=
  3 * logBarrier (b ^ 4) - b ^ 3 * logBarrier b - b ^ 2 * logBarrier (b ^ 2)

def lambdaAuxiliaryDerivative (b : ℝ) : ℝ :=
  12 * b ^ 3 / (1 - b ^ 4) - 3 * b ^ 2 * logBarrier b - b ^ 3 / (1 - b) -
    2 * b * logBarrier (b ^ 2) - 2 * b ^ 3 / (1 - b ^ 2)

@[simp] theorem lambdaAuxiliary_zero : lambdaAuxiliary 0 = 0 := by
  simp [lambdaAuxiliary]

theorem hasDerivAt_lambdaAuxiliary {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasDerivAt lambdaAuxiliary (lambdaAuxiliaryDerivative b) b := by
  have hb2 := sq_lt_one_of_nonneg hb0 hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have h1 := hasDerivAt_logBarrier hb1
  have h2 := (hasDerivAt_logBarrier hb2).comp b (h := fun t : ℝ => t ^ 2) (hasDerivAt_pow 2 b)
  have h4 := (hasDerivAt_logBarrier hb4).comp b (h := fun t : ℝ => t ^ 4) (hasDerivAt_pow 4 b)
  have hd := ((h4.const_mul 3).sub ((hasDerivAt_pow 3 b).mul h1)).sub
    ((hasDerivAt_pow 2 b).mul h2)
  convert! hd using 1
  simp only [lambdaAuxiliaryDerivative, Function.comp_apply]
  ring

theorem lambdaAuxiliaryDerivative_factor {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    lambdaAuxiliaryDerivative b = b ^ 3 / (1 - b ^ 4) * lambdaDerivativeFactor b := by
  have hb2 := sq_lt_one_of_nonneg hb0.le hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have hne : b ≠ 0 := hb0.ne'
  have hne2 : b ^ 2 ≠ 0 := pow_ne_zero _ hne
  have h1 : 1 - b ≠ 0 := by linarith
  have h2 : 1 - b ^ 2 ≠ 0 := by linarith
  have h4 : 1 - b ^ 4 ≠ 0 := by linarith
  simp only [lambdaAuxiliaryDerivative, lambdaDerivativeFactor, logBarrier,
    lambda_of_ne_zero hne, lambda_of_ne_zero hne2]
  field_simp
  ring

theorem lambdaDerivativeFactor_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < lambdaDerivativeFactor b := by
  have hp := lambdaCertificate_pos hb0 hb1.le
  have hf := lambda_polynomial_le_factor hb0 hb1
  unfold lambdaPolynomial at hp
  linarith

theorem lambdaAuxiliaryDerivative_nonneg {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliaryDerivative b := by
  rw [lambdaAuxiliaryDerivative_factor hb0 hb1]
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) (sq_lt_one_of_nonneg hb0.le hb1)
    nlinarith
  exact mul_nonneg (div_nonneg (pow_nonneg hb0.le _) (sub_nonneg.mpr hb4.le))
    (lambdaDerivativeFactor_pos hb0.le hb1).le

theorem monotoneOn_lambdaAuxiliary : MonotoneOn lambdaAuxiliary (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun b hb => (hasDerivAt_lambdaAuxiliary hb.1 hb.2).continuousAt.continuousWithinAt)
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact (hasDerivAt_lambdaAuxiliary hb.1.le hb.2).hasDerivWithinAt
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact lambdaAuxiliaryDerivative_nonneg hb.1 hb.2

theorem lambdaAuxiliary_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliary b := by
  simpa using monotoneOn_lambdaAuxiliary
    (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hb0, hb1⟩ hb0

theorem lambdaAuxiliary_eq (b : ℝ) :
    lambdaAuxiliary b = b ^ 4 * (3 * lambda (b ^ 4) - lambda b - lambda (b ^ 2)) := by
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [lambdaAuxiliary, hM, hM, hM]
  ring

theorem lambda_add_sq_le (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    lambda b + lambda (b ^ 2) ≤ 3 * lambda (b ^ 4) := by
  by_cases hb : b = 0
  · subst b
    norm_num
  have h := lambdaAuxiliary_nonneg hb0 hb1
  rw [lambdaAuxiliary_eq] at h
  have hp : 0 < b ^ 4 := pow_pos (lt_of_le_of_ne hb0 (Ne.symm hb)) _
  have ht := nonneg_of_mul_nonneg_right h hp
  linarith

theorem lambda_sqrt_add_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lambda (Real.sqrt q) + lambda q ≤ 3 * lambda (q ^ 2) := by
  have hsq := Real.sq_sqrt hq0
  have hq : Real.sqrt q < 1 := by nlinarith [Real.sqrt_nonneg q]
  have h := lambda_add_sq_le (Real.sqrt q) (Real.sqrt_nonneg q) hq
  have hfour : (Real.sqrt q) ^ 4 = q ^ 2 := by nlinarith [sq_nonneg (Real.sqrt q)]
  simpa only [hsq, hfour] using h

theorem concave_perspective_exchange (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Ioi 0) f)
    (w q : ℝ) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1) :
    f 1 + f (w - q) ≤ f w + f (1 - q) := by
  let a := q / (1 - w + q)
  let b := (1 - w) / (1 - w + q)
  have hr : 0 < 1 - w + q := by linarith
  have ha : 0 ≤ a := div_nonneg hq0.le hr.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hw1) hr.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hab' : b + a = 1 := by linarith
  have hp1 : a * 1 + b * (w - q) = w := by dsimp [a, b]; field_simp; ring
  have hp2 : b * 1 + a * (w - q) = 1 - q := by dsimp [a, b]; field_simp; ring
  have h1 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) ha hb hab
  have h2 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) hb ha hab'
  simp only [smul_eq_mul, hp1, hp2] at h1 h2
  calc
    f 1 + f (w - q) = (a * f 1 + b * f (w - q)) +
        (b * f 1 + a * f (w - q)) := by
      calc
        _ = (a + b) * f 1 + (a + b) * f (w - q) := by rw [hab]; ring
        _ = _ := by ring
    _ ≤ f w + f (1 - q) := add_le_add h1 h2

theorem perspective_kernel_upper (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1)
    (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) := by
  have he := concave_perspective_exchange _ hconc w q hq0 hqw hw1
  have hn : 0 ≤ (w - q) * f (x / (w - q)) :=
    mul_nonneg (sub_nonneg.mpr hqw.le) (hf0 _ (div_pos hx (sub_pos.mpr hqw)))
  simp only [one_mul, div_one, Real.log_one, mul_zero, sub_zero] at he
  nlinarith

theorem lt_weight_of_le_weight_sq {w q : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq1 : q < 1) (hqw : q ≤ w ^ 2) : q < w := by
  rcases eq_or_lt_of_le hw1 with rfl | hwlt
  · simpa using hq1
  · have hsq : w ^ 2 < w := by nlinarith [mul_pos hw0 (sub_pos.mpr hwlt)]
    exact hqw.trans_lt hsq

theorem lambda_trapezoid_bound (w q : ℝ)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hqdiv0 : 0 ≤ q / w := div_nonneg hq0 hw0.le
  have hqdiv1 : q / w < 1 := (div_lt_one hw0).mpr hlt
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q < 1 := by nlinarith
  have hsw : Real.sqrt q ≤ w := by nlinarith
  have hdivsqrt : q / w ≤ Real.sqrt q := by
    apply (div_le_iff₀ hw0).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hsw)]
  have hl1 := monotoneOn_lambda ⟨hqdiv0, hqdiv1⟩ ⟨hs0, hs1⟩ hdivsqrt
  have hl2 : w * lambda q ≤ lambda q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (lambda_nonneg hq0 hq1)]
  have hls := lambda_sqrt_add_le q hq0 hq1
  have hsum : lambda (q / w) + w * lambda q ≤ 3 * lambda (q ^ 2) := by linarith
  have hcoef : 0 ≤ q * (1 - w) / (3 * w) :=
    div_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hw1)) (mul_nonneg (by norm_num) hw0.le)
  have hm := mul_le_mul_of_nonneg_left hsum hcoef
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [hM, hM]
  convert hm using 1 <;> field_simp

theorem perspective_inequality_of_adjusted_concave (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · subst q
    have hn := mul_nonneg hw0.le (hf0 _ (div_pos hx hw0))
    simpa using neg_nonpos.mpr hn
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hk := perspective_kernel_upper f x w q hx hq hlt hw1 hf0 hconc
  have ht := perspective_log_trapezoid q w hq0 hlt hw1
  have hl := lambda_trapezoid_bound w q hw0 hw1 hq0 hq1 hqw
  have hc : (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) ≤
      (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) := by
    unfold logBarrier
    nlinarith
  exact hk.trans (hc.trans hl)

theorem LSecondDeriv_curvature_bound {x : ℝ} (hx : 0 < x) :
    x ^ 2 * LSecondDeriv x ≤ 2 / 3 := by
  by_cases hxl : x < ell
  · simpa only [LSecondDeriv, ite_eq_left hxl] using L_curvature_bound ⟨hx, hxl⟩
  · simp only [LSecondDeriv, ite_eq_right hxl, mul_zero]
    norm_num

theorem concaveOn_L_logCorrectedPerspective (x : ℝ) (hx : 0 < x) :
    ConcaveOn ℝ (Ioi 0)
      (fun v => v * L (x / v) - (2 / 3 : ℝ) * v * Real.log v) := by
  exact concaveOn_logCorrectedPerspective L LDeriv LSecondDeriv x (2 / 3) ell
    hx ell_pos (fun y hy => hasDerivAt_L hy) continuousOn_LDeriv
    (fun y hy hne => hasDerivAt_LDeriv hy hne)
    (fun y hy _ => LSecondDeriv_curvature_bound hy)

theorem perspective_inequality (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) :=
  perspective_inequality_of_adjusted_concave L x w q hx hw0 hw1 hq0 hq1 hqw
    (fun _ ht => L_nonneg ht) (concaveOn_L_logCorrectedPerspective x hx)

end LeanBlast.CourtadeKumar

end

end OAI
