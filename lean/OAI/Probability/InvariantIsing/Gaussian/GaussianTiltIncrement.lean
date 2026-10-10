import OAI.Probability.InvariantIsing.Gaussian.GaussianExponentialShift

namespace OAI

/-! The canonical one-step Gaussian increment satisfies the sharp
exponential bound from the magnetic replacement argument. Its cost is
proportional to variance, so it can be summed over arbitrary depths. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem gaussian_tilt_increment_mgf (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (hLip : ∀ x y, |F x - F y| ≤ |x - y|) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ x, Real.exp (t * x)
      ∂(gaussianReal 0 v).tilted (fun x => b * F (z + x))) ≤
        Real.exp ((t ^ 2 / 2 + |t|) * v) := by
  let U := fun x => Real.exp (b * F (z + x))
  have hi : Integrable U (gaussianReal 0 v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 v)
      (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) b
  have hp : 0 < ∫ x, U x ∂gaussianReal 0 v :=
    integral_exp_pos _ (fun x => F (z + x)) hi
  have hs : Integrable (fun x => U (x + t * v)) (gaussianReal 0 v) := by
    have hx := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 v)
      (hF.comp (measurable_const.add measurable_id)) (hG.add_left (z + t * v)) b
    convert hx using 1
    funext x
    change Real.exp (b * F (z + (x + t * v))) =
      Real.exp (b * F ((z + t * v) + x))
    rw [show z + (x + t * v) = (z + t * v) + x by ring]
  have hbound (x : ℝ) : U (x + t * v) ≤ Real.exp (|t| * v) * U x := by
    dsimp only [U]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := (abs_le.mp (hLip (z + (x + t * v)) (z + x))).2
    rw [show z + (x + t * v) - (z + x) = t * v by ring,
      abs_mul, abs_of_nonneg v.coe_nonneg] at hl
    have hmul := mul_le_mul_of_nonneg_left hl hb0
    have hb := mul_le_mul_of_nonneg_right hb1 (mul_nonneg (abs_nonneg t) v.coe_nonneg)
    nlinarith
  have hshift : (∫ x, U (x + t * v) ∂gaussianReal 0 v) ≤
      Real.exp (|t| * v) * ∫ x, U x ∂gaussianReal 0 v := by
    simpa only [integral_const_mul] using integral_mono hs (hi.const_mul _) hbound
  rw [integral_tilted_eq_div]
  have he : (∫ x, Real.exp (b * F (z + x)) * Real.exp (t * x) ∂gaussianReal 0 v) =
      Real.exp (t ^ 2 * v / 2) * ∫ x, U (x + t * v) ∂gaussianReal 0 v := by
    rw [show (fun x => Real.exp (b * F (z + x)) * Real.exp (t * x)) =
      (fun x => Real.exp (t * x) * U x) by funext x; exact mul_comm _ _]
    exact gaussian_exp_linear_shift v t U ((hF.comp (measurable_const.add measurable_id)).const_mul b).exp
  rw [he]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ Real.exp (t ^ 2 * v / 2) * (Real.exp (|t| * v) * ∫ x, U x ∂gaussianReal 0 v) :=
      mul_le_mul_of_nonneg_left hshift (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

end InvariantIsing

end

end OAI
