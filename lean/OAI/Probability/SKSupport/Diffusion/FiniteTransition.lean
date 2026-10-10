import Mathlib
import OAI.Probability.SKSupport.Diffusion.ProgressiveBrownian
import OAI.Probability.SKSupport.Diffusion.FiniteFeedback
import OAI.Probability.SKSupport.Parabolic.TiltedTransition

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma BoundedLipschitzDrift.solution_zero (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) (w : Ω) :
    b.solution W.driver 0 w=0 := by
  rw [b.solution_eq _ W.driver_progressive]
  simp only [W.driver_zero,NNReal.coe_zero,intervalIntegral.integral_same,add_zero]

lemma Heat.backwardBoundary_step {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    varianceLogHeat (c i) (h:ℝ) (backwardBoundary c h f N (i+1))=backwardBoundary c h f N i := by
  have hn : N-i=(N-(i+1))+1 := by omega
  funext x
  unfold backwardBoundary
  rw [varianceLogHeat_eq_logSemigroup_toNNReal (cascade_regular hf hLip c h _ _).smooth.continuous.measurable,
    Real.toNNReal_coe]
  simp only [hn,cascade]

lemma Heat.exp_varianceLogHeat {f : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K f)
    {c : ℝ} (hc : c ≠ 0) (t x : ℝ) :
    Real.exp (c*varianceLogHeat c t f x)=varianceHeat t (fun y => Real.exp (c*f y)) x := by
  simp only [varianceLogHeat,ite_eq_right hc]
  rw [mul_div_cancel₀ _ hc,Real.exp_log (varianceHeat_exp_pos hLip c t x)]

theorem finite_transition_tilted (W : BrownianSystem Ω) {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i+1:ℕ)*h) w) ∂W.law)=
      ∫ w, varianceTilted (c i) h (backwardBoundary c h f N (i+1)) g
        ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h) w) ∂W.law := by
  have ht : (i:ℝ≥0)*h ≤ ((i+1:ℕ):ℝ≥0)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) h.coe_nonneg
  have hh := expected_transition_tiltedMean W (finiteFeedback hf hLip c h N 0)
    (cascade_regular hf hLip c h (N-(i+1)) (i+1)) (cascade_lipschitz hLip c h _ _) hg (c i).coe_nonneg ht
    (fun t htt x => by
      have he := finiteFeedback_step hf hLip c h hi (t := t) (by simpa only [NNReal.coe_mul,NNReal.coe_natCast] using htt) x
      simpa only [NNReal.coe_mul,NNReal.coe_natCast,backwardBoundary] using he)
  have he : ((((i+1:ℕ):ℝ≥0)*h:ℝ≥0):ℝ)-(((i:ℝ≥0)*h:ℝ≥0):ℝ)=(h:ℝ) := by push_cast;ring
  simpa only [he,backwardBoundary] using hh

lemma Heat.varianceLogHeat_add {f : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K f)
    {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    varianceLogHeat c (a+b) f=varianceLogHeat c a (varianceLogHeat c b f) := by
  funext x
  rw [varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable,
    varianceLogHeat_eq_logSemigroup_toNNReal (varianceLogHeat_lipschitz hLip hc b).continuous.measurable]
  have he : varianceLogHeat c b f=logSemigroup c (Real.toNNReal b) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable c b)
  rw [he,Real.toNNReal_add ha hb,logSemigroup_add hLip]

end ZeroTemperatureSK

end
end

end OAI
