import OAI.Analysis.IrrationalRotation.Analysis.ScalarRectangleDiscrepancy
import OAI.Analysis.IrrationalRotation.Analysis.BVDiscrepancy

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ScalarRectangles

theorem scalar_bv_discrepancy (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (f g : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ t, f (Int.fract ((n : ℝ) * t)) * g (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y)‖ ≤
      (29 / (m : ℝ) ^ 80) *
        (sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
          (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) +
          (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN₀
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)
  have hX : Measurable (fun t => Int.fract ((n : ℝ) * t)) :=
    measurable_fract.comp (measurable_const_mul (n : ℝ))
  have hY : Measurable (fun t => Int.fract ((n' : ℝ) * t)) :=
    measurable_fract.comp (measurable_const_mul (n' : ℝ))
  have hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ t, BVDiscrepancy.tail a (Int.fract ((n : ℝ) * t)) *
        BVDiscrepancy.tail b (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ 29 / (m : ℝ) ^ 80 := by
    intro a ha b hb
    simpa only [BVDiscrepancy.tail, Complex.ofReal_mul] using
      scalar_tail_rectangles_integral m hm N₀ N hN₀ hN hNm n n' hn hn' hsep a b ha hb
  have h := BVDiscrepancy.boundedVariation_discrepancy
    (UniformIntervalPhase.lambdaLaw N₀) hX hY
    (sampled_fraction_absolutelyContinuous N₀ n hN₀ (hmp.trans_le hn))
    (sampled_fraction_absolutelyContinuous N₀ n' hN₀ (hmp.trans_le hn'))
    (by positivity : (0 : ℝ) ≤ 29 / (m : ℝ) ^ 80) hrect f g hf hg
  simpa only [BVDiscrepancy.unitMeasure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

end Invariant233.ScalarRectangles

end

end OAI
