import OAI.Analysis.LipschitzHilbert.Fourier.FrequencyKernelTranslations

namespace OAI

/-! Joint parameter dependence and a uniform bound for the separated
frequency multiplier. These are used to interchange its parameter and
physical-space integrals. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem modulatedFrequency_eq_window (F : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) :
    modulatedFrequency F nu l W theta center =
      modulatedFrequencyWindow F (nu 0*l) (nu 0*l*theta+nu 1*W) (-(nu 1*W*center)) := by
  funext omega
  rw [modulatedFrequencyWindow_apply]
  dsimp only [modulatedFrequency,frequencyCharacter,symbolX,symbolY]
  rw [Real.fourierChar_apply,Real.fourierChar_apply,Real.fourierChar_apply]
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem planarInverse_modulated_frequency (F : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) (x : ℝ×ℝ) :
    planarInverse (modulatedFrequency F nu l W theta center) x =
      (Real.fourierChar (-(nu 1*W*center)):ℂ)*
        planarInverseSchwartz F (x+(nu 0*l,nu 0*l*theta+nu 1*W)) := by
  rw [modulatedFrequency_eq_window,←planarInverseSchwartz_apply,
    planarInverse_modulatedFrequencyWindow]

theorem modulated_inverse_joint_continuous (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      planarInverse (modulatedFrequency F p.1 l W theta center) p.2) := by
  simp_rw [planarInverse_modulated_frequency]
  fun_prop

theorem planarInverse_norm_le (F : ℝ×ℝ → ℂ) (x : ℝ×ℝ) :
    ‖planarInverse F x‖ ≤ ∫ omega, ‖F omega‖ ∂planeMeasure := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Circle.smul_def,smul_eq_mul,norm_mul,Circle.norm_coe,one_mul]

theorem modulated_inverse_norm_le (F : ℝ×ℝ → ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) (x : ℝ×ℝ) :
    ‖planarInverse (modulatedFrequency F nu l W theta center) x‖ ≤
      ∫ omega, ‖F omega‖ ∂planeMeasure := by
  apply (planarInverse_norm_le _ x).trans_eq
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [modulatedFrequency,norm_mul,norm_frequencyCharacter,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
