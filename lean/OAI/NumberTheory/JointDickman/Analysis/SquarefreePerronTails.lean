import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # The two tails of the normalized squarefree Perron integral -/
namespace JointDickman
open Complex MeasureTheory Set

theorem squarefreeNormalizedPerron_tail_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L c T ε : ℝ), 0 < c → c ≤ 1 → 3 < T → |ε| = 1 →
      ‖∫ t : ℝ in Ioi T, squarefreeNormalizedPerron z L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)‖ ≤
        2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeNormalizedPerron_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro L c T ε hc hc1 hT hε
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun t : ℝ => C*Real.exp (L*c)*t^(-3/2:ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0).const_mul _
  calc
    _ ≤ ∫ t : ℝ in Ioi T, C*Real.exp (L*c)*t^(-3/2:ℝ) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT0.trans ht
      have hp := hb L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)
        (by simpa using hc) (by simpa using hc1)
        (by simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
          zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos ht0] using hT.trans ht)
      simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,add_im,mul_im,mul_one,zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos ht0] using hp
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0]
      norm_num
      ring

end JointDickman

end OAI
