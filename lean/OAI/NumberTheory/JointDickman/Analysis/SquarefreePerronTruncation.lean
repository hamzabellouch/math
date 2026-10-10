import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronIntegrable
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronTails
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace OAI

/-! # Quantitative truncation of the normalized squarefree Perron line -/
namespace JointDickman
open Complex MeasureTheory Set

theorem perron_normalization_norm :
    ‖(1/(2*(Real.pi:ℂ)*I):ℂ)‖ = 1/(2*Real.pi) := by
  simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]

theorem squarefreeNormalizedPerron_truncation_bound {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L c T : ℝ, 0 < c → c ≤ 1 → 3 < T →
      ‖VerticalIntegral' (squarefreeNormalizedPerron z L) c -
        (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T‖ ≤
        C*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeNormalizedPerron_tail_bound hz hz1
  refine ⟨4*C/(2*Real.pi),by positivity,?_⟩
  intro L c T hc hc1 hT
  let P := squarefreeNormalizedPerron z L
  have hlo : ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [←integral_comp_neg_Ioi T (fun t : ℝ => P ((c:ℂ)+(t:ℂ)*I))]
    simpa only [neg_one_mul] using hb L c T (-1) hc hc1 hT (by norm_num)
  have hhi : ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    simpa only [one_mul] using hb L c T 1 hc hc1 hT (by norm_num)
  have heq : VerticalIntegral' P c -
      (1/(2*(Real.pi:ℂ)*I))*VIntegral P c (-T) T =
      (1/(2*(Real.pi:ℂ)*I))*I*
        ((∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)) +
         (∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I))) := by
    rw [VerticalIntegral',verticalIntegral_split_three (-T) T
      (squarefreeNormalizedPerron_integrable hz hz1 hc)]
    simp only [smul_eq_mul]
    ring
  rw [heq,norm_mul,norm_mul,perron_normalization_norm,norm_I,mul_one]
  calc
    _ ≤ (1/(2*Real.pi))*(
      ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ +
      ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1/(2*Real.pi))*(2*C*Real.exp (L*c)*T^(-1/2:ℝ) +
        2*C*Real.exp (L*c)*T^(-1/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
