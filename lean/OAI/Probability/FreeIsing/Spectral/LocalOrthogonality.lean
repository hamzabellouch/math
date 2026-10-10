import Mathlib

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem indepFun_of_disjoint_finite_blocks (s t : Finset ι) (hst : Disjoint s t)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (∀ i : s, X i) → α) (g : (∀ i : t, X i) → β)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ∀ i, X i => f (fun i => U i))
      (fun U : ∀ i, X i => g (fun i => U i)) (Measure.infinitePi μ) := by
  have hind : iIndepFun (fun i (U : ∀ i, X i) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact (hind.indepFun_finset s t hst (fun i => measurable_pi_apply i)).comp hf hg

theorem integral_mul_eq_of_disjoint_finite_blocks (s t : Finset ι) (hst : Disjoint s t)
    (f : (∀ i : s, X i) → ℝ) (g : (∀ i : t, X i) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    (∫ U, f (fun i => U i) * g (fun i => U i) ∂Measure.infinitePi μ) =
      (∫ U, f (fun i => U i) ∂Measure.infinitePi μ) *
      (∫ U, g (fun i => U i) ∂Measure.infinitePi μ) := by
  apply (indepFun_of_disjoint_finite_blocks μ s t hst f g hf hg).integral_fun_mul_eq_mul_integral
  all_goals exact Measurable.aestronglyMeasurable (by fun_prop)

theorem integral_mul_eq_zero_of_disjoint_finite_blocks (s t : Finset ι)
    (hst : Disjoint s t) (f : (∀ i : s, X i) → ℝ) (g : (∀ i : t, X i) → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hzero : (∫ U, f (fun i => U i) ∂Measure.infinitePi μ) = 0) :
    (∫ U, f (fun i => U i) * g (fun i => U i) ∂Measure.infinitePi μ) = 0 := by
  rw [integral_mul_eq_of_disjoint_finite_blocks μ s t hst f g hf hg, hzero, zero_mul]

theorem integral_mul_eq_zero_of_ae_finite_blocks (s t : Finset ι)
    (hst : Disjoint s t) (f g : (∀ i, X i) → ℝ)
    (F : (∀ i : s, X i) → ℝ) (G : (∀ i : t, X i) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hf : f =ᵐ[Measure.infinitePi μ] fun U => F (fun i => U i))
    (hg : g =ᵐ[Measure.infinitePi μ] fun U => G (fun i => U i))
    (hfm : AEStronglyMeasurable f (Measure.infinitePi μ))
    (hgm : AEStronglyMeasurable g (Measure.infinitePi μ))
    (hzero : (∫ U, f U ∂Measure.infinitePi μ) = 0) :
    (∫ U, f U * g U ∂Measure.infinitePi μ) = 0 := by
  have hind := (indepFun_of_disjoint_finite_blocks μ s t hst F G hF hG).congr hf.symm hg.symm
  rw [hind.integral_fun_mul_eq_mul_integral hfm hgm, hzero, zero_mul]

theorem inner_eq_zero_of_disjoint_finite_blocks (s t : Finset ι)
    (hst : Disjoint s t) (f g : Lp ℝ 2 (Measure.infinitePi μ))
    (F : (∀ i : s, X i) → ℝ) (G : (∀ i : t, X i) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hf : f =ᵐ[Measure.infinitePi μ] fun U => F (fun i => U i))
    (hg : g =ᵐ[Measure.infinitePi μ] fun U => G (fun i => U i))
    (hzero : (∫ U, f U ∂Measure.infinitePi μ) = 0) :
    inner ℝ f g = 0 := by
  rw [L2.inner_def]
  simpa [RCLike.inner_apply, mul_comm] using
    integral_mul_eq_zero_of_ae_finite_blocks μ s t hst f g F G hF hG hf hg
      (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g) hzero

section Reindex

variable {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

theorem indepFun_finite_blocks_reindex (s t : Finset ι) (e : ι ≃ ι)
    (hst : Disjoint s (t.map e.toEmbedding))
    (f : (s → A) → ℝ) (g : (t → A) → ℝ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ι → A => f (fun i => U i))
      (fun U : ι → A => g (fun i => U (e i))) (Measure.infinitePi fun _ : ι => ν) := by
  let G : (t.map e.toEmbedding → A) → ℝ := fun U =>
    g (fun i => U ⟨e i, Finset.mem_map.2 ⟨i, i.property, rfl⟩⟩)
  have hG : Measurable G := by
    apply hg.comp
    fun_prop
  simpa [G] using indepFun_of_disjoint_finite_blocks (fun _ : ι => ν)
    s (t.map e.toEmbedding) hst f G hf hG

theorem integral_mul_reindex_eq_zero_of_disjoint (s t : Finset ι) (e : ι ≃ ι)
    (hst : Disjoint s (t.map e.toEmbedding))
    (f : (s → A) → ℝ) (g : (t → A) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hzero : (∫ U, f (fun i => U i) ∂Measure.infinitePi (fun _ : ι => ν)) = 0) :
    (∫ U, f (fun i => U i) * g (fun i => U (e i))
      ∂Measure.infinitePi (fun _ : ι => ν)) = 0 := by
  have hind := indepFun_finite_blocks_reindex ν s t e hst f g hf hg
  rw [hind.integral_fun_mul_eq_mul_integral
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop)), hzero, zero_mul]

end Reindex

end Problem367

end OAI
