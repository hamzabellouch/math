import Mathlib
import OAI.Probability.LogConcave.Analysis.Operator

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

def HasPoincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (β : ℝ) : Prop :=
  ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 μ →
    Integrable (fun x => ‖fderiv ℝ f x‖^2) μ →
    Var[f;μ] ≤ β*∫ x, ‖fderiv ℝ f x‖^2 ∂μ

section
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G] in
lemma derivative_comp_lipschitz_bound {S : E → G} {K : ℝ≥0}
    (hS : ContDiff ℝ 1 S) (hK : LipschitzWith K S)
    {f : G → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    ‖fderiv ℝ (f ∘ S) x‖^2 ≤ (K:ℝ)^2*‖fderiv ℝ f (S x)‖^2 := by
  rw [fderiv_comp x (hf.differentiable (by norm_num) _) (hS.differentiable (by norm_num) _)]
  have hh := (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (S x)) (fderiv ℝ S x)).trans
    (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _))
  have hp := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  simpa only [mul_pow,mul_comm] using hp

theorem HasPoincare.map {μ : Measure E} [IsProbabilityMeasure μ] {β : ℝ}
    (hP : HasPoincare μ β) (hβ : 0 ≤ β) {S : E → G} {K : ℝ≥0}
    (hS : ContDiff ℝ 1 S) (hK : LipschitzWith K S) :
    HasPoincare (μ.map S) (β*(K:ℝ)^2) := by
  intro f hf hm hd
  have hc : ContDiff ℝ 1 (f ∘ S) := hf.comp hS
  have hm' : MemLp (f ∘ S) 2 μ := hm.comp_of_map hS.continuous.aemeasurable
  have hdm : AEStronglyMeasurable (fun y => ‖fderiv ℝ f y‖^2) (μ.map S) :=
    ((hf.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
  have hi : Integrable (fun x => ‖fderiv ℝ f (S x)‖^2) μ :=
    (integrable_map_measure hdm hS.continuous.aemeasurable).1 hd
  have hb := derivative_comp_lipschitz_bound hS hK hf
  have hi' : Integrable (fun x => ‖fderiv ℝ (f ∘ S) x‖^2) μ := by
    apply (hi.const_mul ((K:ℝ)^2)).mono'
      ((hc.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb x
  have hh := hP (f ∘ S) hc hm' hi'
  rw [variance_map hf.continuous.aemeasurable hS.continuous.aemeasurable,
    integral_map hS.continuous.aemeasurable hdm]
  calc
    _ ≤ β*∫ x, ‖fderiv ℝ (f ∘ S) x‖^2 ∂μ := hh
    _ ≤ β*∫ x, (K:ℝ)^2*‖fderiv ℝ f (S x)‖^2 ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono hi' (hi.const_mul _) hb) hβ
    _ = _ := by rw [integral_const_mul]; ring

omit [BorelSpace E] in
lemma HasPoincare.mono {μ : Measure E} {β γ : ℝ}
    (hP : HasPoincare μ β) (h : β ≤ γ) : HasPoincare μ γ := by
  intro f hf hm hd
  exact (hP f hf hm hd).trans (mul_le_mul_of_nonneg_right h
    (integral_nonneg (fun _ => sq_nonneg _)))

lemma HasPoincare.lipschitz_variance {μ : Measure E} [IsProbabilityMeasure μ] {β : ℝ}
    (hP : HasPoincare μ β) (hβ : 0 ≤ β) {f : E → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f) (hm : MemLp f 2 μ) :
    Var[f;μ] ≤ β*(K:ℝ)^2 := by
  have hb (x : E) : ‖fderiv ℝ f x‖^2 ≤ (K:ℝ)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
  have hi : Integrable (fun x => ‖fderiv ℝ f x‖^2) μ :=
    Integrable.mono' (integrable_const ((K:ℝ)^2))
      ((hf.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hb x))
  apply (hP f hf hm hi).trans
  apply mul_le_mul_of_nonneg_left _ hβ
  simpa only [integral_const,probReal_univ,one_smul] using integral_mono hi (integrable_const _) hb
end
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory

theorem Primitive.hasPoincare {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) :
    HasPoincare (gibbs (primitivePotential F x r))
      ((Real.pi^2/8)*(2/(1-(lam:ℝ)*r^2))) := by
  have : IsProbabilityMeasure (gibbs (primitivePotential F x r)) :=
    probability_gibbs_of_partition
      (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
      (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  intro f hf hm hd
  exact PoincareCutoff.extend _ (fun g hg hc => hF.poincare_compact x hr hl hg hc) hf hm hd
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
