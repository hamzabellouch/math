import OAI.NumberTheory.JointDickman.Analysis.FractionalCutJump
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

namespace OAI

/-! # Finite rectangles on either side of the fractional-power cut -/
namespace JointDickman
open Complex Set

noncomputable def fractionalContourIntegrand (z : ℝ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  F w * fractionalPowerKernel z w

theorem fractionalPower_differentiableAt (z : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
    DifferentiableAt ℂ (fractionalPowerKernel z) w := by
  change DifferentiableAt ℂ (fun w : ℂ => exp (-(z:ℂ)*log w)) w
  exact ((differentiableAt_const _).mul (Complex.differentiableAt_log hw)).cexp

theorem fractionalContour_rectangles {z η c T ε : ℝ}
    (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (hεT : ε < T)
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I))) :
    (VIntegral (fractionalContourIntegrand z F) c ε T +
       VIntegral (fractionalContourIntegrand z F) c (-T) (-ε)) -
      (VIntegral (fractionalContourIntegrand z F) (-η) ε T +
       VIntegral (fractionalContourIntegrand z F) (-η) (-T) (-ε)) =
      HIntegral (fractionalContourIntegrand z F) (-η) c T -
      HIntegral (fractionalContourIntegrand z F) (-η) c (-T) +
      HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
      HIntegral (fractionalContourIntegrand z F) (-η) c ε := by
  have hηc : -η ≤ c := by linarith
  have hT : 0 < T := lt_trans hε hεT
  have hupper : Rectangle (-(η:ℂ)+(ε:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) ⊆
      Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) := by
    simpa only [Complex.ofReal_neg,sub_eq_add_neg,neg_mul] using
      (RectSubRect (x₀ := -η) (x₁ := -η) (x₂ := c) (x₃ := c)
        (y₀ := -T) (y₁ := ε) (y₂ := T) (y₃ := T)
        le_rfl hηc le_rfl (by linarith) hεT.le le_rfl)
  have hlower : Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)-(ε:ℂ)*I) ⊆
      Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) := by
    simpa only [Complex.ofReal_neg,sub_eq_add_neg,neg_mul] using
      (RectSubRect (x₀ := -η) (x₁ := -η) (x₂ := c) (x₃ := c)
        (y₀ := -T) (y₁ := -T) (y₂ := -ε) (y₃ := T)
        le_rfl hηc le_rfl le_rfl (by linarith) (by linarith))
  have hu : RectangleIntegral (fractionalContourIntegrand z F)
      (-(η:ℂ)+(ε:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ subset_rfl
    apply (hF.mono hupper).mul
    intro w hw
    apply (fractionalPower_differentiableAt z (Or.inr ?_)).differentiableWithinAt
    have him := (mem_Rect (by simpa using hηc) (by simpa using hεT.le) w).mp hw
    have : ε ≤ w.im := by simpa using him.2.2.1
    linarith
  have hl : RectangleIntegral (fractionalContourIntegrand z F)
      (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)-(ε:ℂ)*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ subset_rfl
    apply (hF.mono hlower).mul
    intro w hw
    apply (fractionalPower_differentiableAt z (Or.inr ?_)).differentiableWithinAt
    have him := (mem_Rect (by simpa using hηc) (by simpa using neg_le_neg hεT.le) w).mp hw
    have : w.im ≤ -ε := by simpa using him.2.2.2
    linarith
  simp only [RectangleIntegral,add_re,sub_re,neg_re,ofReal_re,ofReal_im,
    I_re,I_im,mul_re,mul_im,neg_zero,mul_zero,mul_one,zero_add,
    add_zero,sub_zero,zero_sub,add_im,sub_im,neg_im] at hu hl
  linear_combination hu + hl

end JointDickman

end OAI
