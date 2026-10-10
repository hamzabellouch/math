import Mathlib
import OAI.Probability.SKRatio.Quantization.BinPartition
import OAI.Probability.SKRatio.Variational.FieldFunctional

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar
variable {α : Type*} [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma integral_finite_partition_prod {σ : ℝ → α} (hσ : Measurable σ) (F : α → α → ℝ) :
    (∫ z : ℝ×ℝ, F (σ z.1) (σ z.2) ∂μ.prod μ)=
      ∑ a, ∑ d, binMass μ σ a*binMass μ σ d*F a d := by
  have hi : Integrable (fun z : ℝ×ℝ => F (σ z.1) (σ z.2)) (μ.prod μ) :=
    (memLp_finite_comp ((hσ.comp measurable_fst).prodMk (hσ.comp measurable_snd))
      (fun ad : α×α => F ad.1 ad.2)).integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [integral_prod _ hi]
  simp_rw [integral_finite_partition (μ := μ) hσ (F (σ _))]
  rw [integral_finite_partition (μ := μ) hσ (fun a => ∑ d, binMass μ σ d*F a d)]
  simp only [Finset.mul_sum,mul_assoc]

lemma fieldRadicand_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (h : α → ℝ) (z : Parameters α) (x : ℝ) :
    fieldRadicand μ (fun x => h (σ x)) (pullback μ σ (paramB z))
      (pullback μ σ (paramR z)) x=
      finiteRadicalSq (massRoot μ σ) (fun a => v (h a)) z (σ x) := by
  rw [fieldRadicand_expansion (memLp_pullback hσ _) (memLp_pullback hσ _)
    (measurable_finite_comp hσ h)]
  rw [integral_pullback_energy hσ hm (paramB z) (paramR z)
    (fun a => (v (h (σ x))+v (h a))^2)]
  simp_rw [mul_comm (v (h (σ x))+v (h (σ _))) (pullback μ σ (paramB z) _)]
  rw [integral_pullback hσ hm (paramB z) (fun a => v (h (σ x))+v (h a))]
  rfl

lemma fieldDiagonal_partition {σ : ℝ → α} (hσ : Measurable σ) (h : α → ℝ) (x : ℝ) :
    fieldDiagonal μ (fun x => h (σ x)) x=
      ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h (σ x))+w (h d))) := by
  simp_rw [massRoot_sq]
  exact integral_finite_partition hσ (fun d => v (h d)^2/(w (h (σ x))+w (h d)))

lemma field_diagonal_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (β : ℝ) (h : α → ℝ) (z : Parameters α) :
    (∫ x, (β^2*fieldDiagonal μ (fun x => h (σ x)) x)*
      (pullback μ σ (paramB z) x^2+pullback μ σ (paramR z) x^2) ∂μ)=
      β^2*(∑ a, ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h a)+w (h d)))*
        ((paramB z a)^2+(paramR z a)^2)) := by
  simp_rw [fieldDiagonal_partition hσ h,mul_assoc,integral_const_mul]
  rw [integral_pullback_energy hσ hm (paramB z) (paramR z)
    (fun a => ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h a)+w (h d))))]
  simp only [Finset.sum_mul, mul_assoc]

lemma field_kernel_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (h : α → ℝ) (B : α → ℝ) :
    (∫ z : ℝ×ℝ, pullback μ σ B z.1*kernel (h (σ z.1)) (h (σ z.2))*
      pullback μ σ B z.2 ∂μ.prod μ)=
      ∑ a, ∑ d, massRoot μ σ a*B a*kernel (h a) (h d)*(massRoot μ σ d*B d) := by
  change (∫ z : ℝ×ℝ, (fun a d => (B a/massRoot μ σ a)*kernel (h a) (h d)*
    (B d/massRoot μ σ d)) (σ z.1) (σ z.2) ∂μ.prod μ)=_
  rw [integral_finite_partition_prod (μ := μ) hσ (fun a d => (B a/massRoot μ σ a)*kernel (h a) (h d)*(B d/massRoot μ σ d))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [←massRoot_sq σ a,←massRoot_sq σ d]
  field_simp [(massRoot_pos hm a).ne',(massRoot_pos hm d).ne']

theorem fieldForm_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (β : ℝ) (h : α → ℝ) (z : Parameters α) :
    fieldForm μ β (fun x => h (σ x)) (pullback μ σ (paramB z))
      (pullback μ σ (paramR z))=finiteV β (massRoot μ σ) h z := by
  unfold fieldForm
  rw [field_diagonal_pullback hσ hm β h z,field_kernel_pullback hσ hm]
  simp_rw [fieldRadicand_pullback hσ hm h z]
  rw [integral_pullback hσ hm (paramB z) h,
    integral_pullback hσ hm (paramB z) (fun a => v (h a)),
    integral_pullback hσ hm (paramB z) (fun a => h a*v (h a)),
    integral_pullback hσ hm (paramB z) (fun a => m (h a)*v (h a)),
    integral_pullback hσ hm (paramR z) (fun a => sqrt (finiteRadicalSq (massRoot μ σ) (fun a => v (h a)) z a))]
  have hmean : (∫ x, pullback μ σ (paramB z) x ∂μ)=moment (massRoot μ σ) (paramB z) (fun _ => 1) := by
    simpa only [mul_one] using integral_pullback hσ hm (paramB z) (fun _ => 1)
  rw [hmean]
  unfold finiteV finiteA finiteGaussian moment
  ring

end SKRatio.Bins

end

end OAI
