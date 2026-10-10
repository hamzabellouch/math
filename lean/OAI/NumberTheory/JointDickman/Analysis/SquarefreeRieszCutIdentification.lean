import OAI.NumberTheory.JointDickman.Analysis.ZetaRectanglePrincipal
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszHankelExpansion

namespace OAI

/-! # Identifying the actual cut contribution with the local Riesz expansion -/
namespace JointDickman
open Complex MeasureTheory Set

theorem squarefreeRiesz_cut_identification : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → δ/4 < r → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ z L : ℝ,
        ((Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 (δ/4), (t^(-z):ℝ) • squarefreeRieszKernel z L f (-(t:ℂ)))).re =
        squarefreeRieszLocalHankel z (δ/4) L := by
  obtain ⟨r,hr,hlocal⟩ := squarefreeRieszKernel_local_uniform
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT hδr f hf hf1 he z L
  unfold squarefreeRieszLocalHankel
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have htδ : t < δ := by linarith [ht.2]
  have hs : 1+(-(t:ℂ)) ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T := by
    constructor
    · rw [Metric.mem_ball,dist_eq_norm]
      have heq : (1:ℂ)+(-(t:ℂ))-1 = -(t:ℂ) := by ring
      rw [heq,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
      exact ht.2.trans_lt hδr
    · simp only [zetaOpenRectangle,mem_inter_iff,mem_preimage,add_re,one_re,neg_re,
        ofReal_re,add_im,one_im,neg_im,ofReal_im,neg_zero,add_zero]
      constructor <;> constructor <;> linarith
  rw [hlocal hδ hT hf hf1 he z L (-(t:ℂ)) hs]
  have hexp : exp ((L:ℂ)*(-(t:ℂ))) = (Real.exp (-(L*t)):ℂ) := by
    rw [show (L:ℂ)*(-(t:ℂ)) = (-(L*t):ℝ) by push_cast; ring,Complex.ofReal_exp]
  rw [hexp]
  simp only [Complex.real_smul,Complex.ofReal_mul,sub_eq_add_neg]
  ring

end JointDickman

end OAI
