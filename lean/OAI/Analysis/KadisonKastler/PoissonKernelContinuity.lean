import OAI.Analysis.KadisonKastler.PoissonKernelFormula

namespace OAI

/-! # Quantitative translation continuity of the Poisson kernel -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem realPoissonKernel_eq_cauchyPDFReal (t s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    realPoissonKernel t r s = cauchyPDFReal t (NNReal.mk r hr) s := by
  change r / (Real.pi * ((t - s) ^ 2 + r ^ 2)) =
    Real.pi⁻¹ * r * ((s - t) ^ 2 + r ^ 2)⁻¹
  have hs : (t - s) ^ 2 = (s - t) ^ 2 := by ring
  rw [hs, div_eq_mul_inv, mul_inv]
  ring

theorem realPoissonKernel_nonneg (t s : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ realPoissonKernel t r s := by
  unfold realPoissonKernel
  positivity

theorem integrable_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (realPoissonKernel t r) := by
  have he : realPoissonKernel t r = cauchyPDFReal t (NNReal.mk r hr.le) :=
    funext fun s => realPoissonKernel_eq_cauchyPDFReal t s hr.le
  rw [he]
  exact integrable_cauchyPDFReal t

theorem integral_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ s, realPoissonKernel t r s) = 1 := by
  have he : realPoissonKernel t r = cauchyPDFReal t (NNReal.mk r hr.le) :=
    funext fun s => realPoissonKernel_eq_cauchyPDFReal t s hr.le
  rw [he]
  exact integral_cauchyPDFReal_eq_one t (by
    intro h
    have hh : r = 0 := congrArg (fun (z : NNReal) => (z : ℝ)) h
    exact hr.ne' hh)

/-- A pointwise integrable bound for changing the center while keeping
positive height fixed. -/
theorem abs_realPoissonKernel_sub_le (t u s : ℝ) {r : ℝ} (hr : 0 < r) :
    |realPoissonKernel t r s - realPoissonKernel u r s| ≤
      (|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s) := by
  let a := (t - s) ^ 2 + r ^ 2
  let b := (u - s) ^ 2 + r ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hden : 0 < Real.pi * a * b := by positivity
  have hsum : r * |(u - s) + (t - s)| ≤ a + b := by
    have habs := mul_le_mul_of_nonneg_left (abs_add_le (u - s) (t - s)) hr.le
    have h₁ := sq_nonneg (|t - s| - r)
    have h₂ := sq_nonneg (|u - s| - r)
    dsimp [a, b]
    nlinarith [sq_abs (t - s), sq_abs (u - s), sq_nonneg (t - s), sq_nonneg (u - s)]
  have hab : r * |b - a| ≤ |t - u| * (a + b) := by
    have he : b - a = ((u - s) - (t - s)) * ((u - s) + (t - s)) := by dsimp [a, b]; ring
    have hd : (u - s) - (t - s) = u - t := by ring
    rw [he, abs_mul, hd, abs_sub_comm u t]
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (t - u))]
  have hf : realPoissonKernel t r s - realPoissonKernel u r s =
      (r / (Real.pi * a * b)) * (b - a) := by
    change r / (Real.pi * a) - r / (Real.pi * b) = _
    field_simp
  have hg : (|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s) =
      (1 / (Real.pi * a * b)) * (|t - u| * (a + b)) := by
    change (|t - u| / r) * (r / (Real.pi * a) + r / (Real.pi * b)) = _
    field_simp
    ring
  rw [hf, abs_mul, abs_of_pos (div_pos hr hden), hg]
  calc
    (r / (Real.pi * a * b)) * |b - a| =
        (1 / (Real.pi * a * b)) * (r * |b - a|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)

end

end KadisonKastler

end OAI
