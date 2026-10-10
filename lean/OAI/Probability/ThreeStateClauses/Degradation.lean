import Mathlib
import OAI.Probability.ThreeStateClauses.DiscreteLaw

namespace OAI

/-! Degradation. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α β : Type*}

def kernelJoint (p : PMF α) (K : α → PMF β) : PMF (α × β) :=
  p.bind (fun a ↦ (K a).map (fun b ↦ (a,b)))

lemma kernelJoint_fst (p : PMF α) (K : α → PMF β) :
    (kernelJoint p K).map Prod.fst = p := by
  simp only [kernelJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h (a : α) : ((K a).map (fun _ ↦ a)) = PMF.pure a := PMF.map_const _ _
  simp only [h, PMF.bind_pure]

lemma kernelJoint_snd (p : PMF α) (K : α → PMF β) :
    (kernelJoint p K).map Prod.snd = p.bind K := by
  simp only [kernelJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h (a : α) : ((K a).map (fun b ↦ b)) = K a := PMF.map_id _
  simp only [h]

lemma discreteMarginal_bind (p : Fin 3 → PMF α) (K : α → PMF β) :
    discreteMarginal (fun i ↦ (p i).bind K) = (discreteMarginal p).bind K := by
  simp only [discreteMarginal, PMF.bind_bind]

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma integral_kernelJoint (p : PMF α) (K : α → PMF β) {f : α × β → ℝ} {C : ℝ}
    (hf : ∀ z, |f z| ≤ C) :
    (∫ z, f z ∂(kernelJoint p K).toMeasure) =
      ∫ a, (∫ b, f (a,b) ∂(K a).toMeasure) ∂p.toMeasure := by
  rw [kernelJoint, integral_pmf_bind p _ hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a ↦ integral_pmf_map (K a) _ f)

lemma integral_kernelJoint_fst (p : PMF α) (K : α → PMF β) (f : α → ℝ) :
    (∫ z, f z.1 ∂(kernelJoint p K).toMeasure) = ∫ a, f a ∂p.toMeasure := by
  rw [← integral_pmf_map, kernelJoint_fst]

lemma integral_kernelJoint_snd (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    (∫ z, f z.2 ∂(kernelJoint p K).toMeasure) = ∫ b, f b ∂(p.bind K).toMeasure := by
  rw [← integral_pmf_map, kernelJoint_snd]

lemma discrete_degradation_identity (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3)
    {g : β → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    (∫ z, (discreteMessage p z.1).1 i*g z.2 ∂(kernelJoint (discreteMarginal p) K).toMeasure) =
      ∫ b, (discreteMessage (fun j ↦ (p j).bind K) b).1 i*g b
        ∂(discreteMarginal (fun j ↦ (p j).bind K)).toMeasure := by
  have hb (z : α × β) : |(discreteMessage p z.1).1 i*g z.2| ≤ 3*C := by
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg z.2) (abs_nonneg _) (by norm_num)
  rw [integral_kernelJoint _ _ hb]
  simp only [integral_const_mul]
  have hbound (a : α) : |∫ b, g b ∂(K a).toMeasure| ≤ C := by
    calc
      |∫ b, g b ∂(K a).toMeasure| ≤ ∫ b, |g b| ∂(K a).toMeasure := abs_integral_le_integral_abs
      _ ≤ ∫ _, C ∂(K a).toMeasure := integral_mono (pmf_bounded_integrable (K a) hg).abs
        (integrable_const C) hg
      _ = C := by simp
  rw [discrete_bayes_integral p i hbound, discrete_bayes_integral _ i hg,
    integral_pmf_bind (p i) K hg]

lemma discrete_degradation_centered (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3)
    {g : β → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    (∫ z, ((discreteMessage p z.1).1 i-(discreteMessage (fun j ↦ (p j).bind K) z.2).1 i)*g z.2
      ∂(kernelJoint (discreteMarginal p) K).toMeasure) = 0 := by
  have hb (m : Message) (b : β) : |m.1 i*g b| ≤ 3*C := by
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg b) (abs_nonneg _) (by norm_num)
  simp_rw [sub_mul]
  rw [integral_sub (f := fun z : α × β ↦ (discreteMessage p z.1).1 i*g z.2)
    (g := fun z : α × β ↦ (discreteMessage (fun j ↦ (p j).bind K) z.2).1 i*g z.2)
    (pmf_bounded_integrable _ (fun z ↦ hb _ z.2))
    (pmf_bounded_integrable _ (fun z ↦ hb _ z.2)),
    discrete_degradation_identity p K i hg,
    integral_kernelJoint_snd (f := fun b ↦ (discreteMessage (fun j ↦ (p j).bind K) b).1 i*g b),
    ← discreteMarginal_bind, sub_self]

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI
