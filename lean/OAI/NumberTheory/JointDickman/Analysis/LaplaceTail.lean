import OAI.NumberTheory.JointDickman.Counting.HankelGammaCoefficients

namespace OAI

/-! # Exponentially small tails of the Laplace moments -/
namespace JointDickman
open MeasureTheory Set Filter

 theorem fractional_laplace_tail_bound {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (hη : 0 ≤ η) (j : ℕ) :
    (∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t))) ≤
      Real.exp (-(L*η/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) := by
  have hL2 : 0 < L/2 := by linarith
  have hg := fractional_laplace_integrable hz1 hL2 j
  have hdom : IntegrableOn
      (fun t : ℝ => Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))) (Ioi 0) :=
    hg.const_mul _
  have hsub : Ioi η ⊆ Ioi (0:ℝ) := fun t ht => lt_of_le_of_lt hη ht
  calc
    _ ≤ ∫ t : ℝ in Ioi η,
        Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t))) := by
      apply integral_mono_ae (IntegrableOn.mono_set (fractional_laplace_integrable hz1 hL j) hsub)
        (IntegrableOn.mono_set hdom hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htt : η < t := ht
      have ht0 : 0 < t := hη.trans_lt htt
      have he : Real.exp (-((L/2)*t)) ≤ Real.exp (-(L*η/2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hsplit : Real.exp (-(L*t)) = Real.exp (-((L/2)*t))*Real.exp (-((L/2)*t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      calc
        _ = (t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))*Real.exp (-((L/2)*t)) := by ring
        _ ≤ (t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))*Real.exp (-(L*η/2)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ in Ioi 0,
        Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t))) := by
      apply setIntegral_mono_set hdom
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        positivity
      · exact Eventually.of_forall (fun _ ht => hsub ht)
    _ = _ := by rw [integral_const_mul,fractional_laplace_gamma hz1 hL2 j]; ring

end JointDickman

end OAI
