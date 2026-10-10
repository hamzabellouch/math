import Mathlib
import OAI.Probability.SKBarriers.Calculus.IntervalDifferentiation
import OAI.Probability.SKBarriers.Calculus.BrascampLieb

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem hasDerivAt_neg_log_intervalPartition
    (V V₁ : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (hV₁ : Continuous (Function.uncurry V₁))
    (hd : ∀ x y, HasDerivAt (fun z => V z y) (V₁ x y) x)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    HasDerivAt (fun z => -Real.log (intervalPartition (V z) a b))
      (intervalMean (V x) (V₁ x) a b) x := by
  let p : ℝ → ℝ → ℝ := fun x y => Real.exp (-V x y)
  have hp : Continuous (Function.uncurry p) := Real.continuous_exp.comp hV.neg
  have hp₁ : Continuous (fun z : ℝ × ℝ => -V₁ z.1 z.2 * p z.1 z.2) := hV₁.neg.mul hp
  have hpd : ∀ z y, HasDerivAt (fun w => p w y) (-V₁ z y * p z y) z := by
    intro z y
    convert! (hd z y).neg.exp using 1
    dsimp [p]
    ring
  have hZ := hasDerivAt_intervalIntegral p (fun z y => -V₁ z y * p z y) hp hp₁ hpd a b x
  have hZ₀ : 0 < intervalPartition (V x) a b :=
    intervalPartition_pos (hV.comp (continuous_const.prodMk continuous_id)) hab
  have heq : (∫ y in a..b, -V₁ x y * p x y) = -(∫ y in a..b, V₁ x y * p x y) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  rw [heq] at hZ
  convert! (hZ.log (ne_of_gt hZ₀)).neg using 1
  dsimp only [intervalMean, intervalPartition, p]
  ring

theorem hasDerivAt_interval_score
    (V V₁ V₂ : ℝ → ℝ → ℝ) (hV : Continuous (Function.uncurry V))
    (hV₁ : Continuous (Function.uncurry V₁)) (hV₂ : Continuous (Function.uncurry V₂))
    (hd : ∀ x y, HasDerivAt (fun z => V z y) (V₁ x y) x)
    (hd₁ : ∀ x y, HasDerivAt (fun z => V₁ z y) (V₂ x y) x)
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    HasDerivAt (fun z => intervalMean (V z) (V₁ z) a b)
      (intervalMean (V x) (V₂ x) a b -
        (intervalMean (V x) (fun y => V₁ x y ^ 2) a b -
          (intervalMean (V x) (V₁ x) a b)^2)) x := by
  let p : ℝ → ℝ → ℝ := fun x y => Real.exp (-V x y)
  have hp : Continuous (Function.uncurry p) := Real.continuous_exp.comp hV.neg
  have hp₁ : Continuous (fun z : ℝ × ℝ => -V₁ z.1 z.2 * p z.1 z.2) := hV₁.neg.mul hp
  have hpd : ∀ z y, HasDerivAt (fun w => p w y) (-V₁ z y * p z y) z := by
    intro z y
    convert! (hd z y).neg.exp using 1
    dsimp [p]
    ring
  have hA : Continuous (fun z : ℝ × ℝ => V₁ z.1 z.2 * p z.1 z.2) := hV₁.mul hp
  have hA₁ : Continuous (fun z : ℝ × ℝ => (V₂ z.1 z.2 - V₁ z.1 z.2^2)*p z.1 z.2) :=
    (hV₂.sub (hV₁.pow 2)).mul hp
  have hAd : ∀ z y, HasDerivAt (fun w => V₁ w y * p w y)
      ((V₂ z y - V₁ z y^2)*p z y) z := by
    intro z y
    convert! (hd₁ z y).fun_mul (hpd z y) using 1
    ring
  have hZ := hasDerivAt_intervalIntegral p (fun z y => -V₁ z y * p z y) hp hp₁ hpd a b x
  have hN := hasDerivAt_intervalIntegral (fun z y => V₁ z y*p z y)
    (fun z y => (V₂ z y - V₁ z y^2)*p z y) hA hA₁ hAd a b x
  have hZ₀ : 0 < intervalPartition (V x) a b :=
    intervalPartition_pos (hV.comp (continuous_const.prodMk continuous_id)) hab
  have heqZ : (∫ y in a..b, -V₁ x y * p x y) = -(∫ y in a..b, V₁ x y * p x y) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  have heqN : (∫ y in a..b, (V₂ x y - V₁ x y^2)*p x y) =
      (∫ y in a..b, V₂ x y*p x y) - (∫ y in a..b, V₁ x y^2*p x y) := by
    simp_rw [sub_mul]
    apply intervalIntegral.integral_sub
    · exact ((hV₂.comp (continuous_const.prodMk continuous_id)).mul
        (hp.comp (continuous_const.prodMk continuous_id))).intervalIntegrable a b
    · exact (((hV₁.comp (continuous_const.prodMk continuous_id)).pow 2).mul
        (hp.comp (continuous_const.prodMk continuous_id))).intervalIntegrable a b
  rw [heqZ] at hZ
  rw [heqN] at hN
  convert! hN.fun_div hZ (ne_of_gt hZ₀) using 1
  dsimp only [intervalMean, intervalPartition, p]
  field_simp
  ring
end SK.Analytic

end
end
end
end
end

end OAI
