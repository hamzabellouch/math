import OAI.Probability.InvariantIsing.Fields.MarkEndpointKernel

namespace OAI

/-! Bounded endpoint observables of independent and shared ancestor paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {N : ℕ}

def markPairEndpoint (n : ℕ) (z₁ z₂ : Fin N → ℝ)
    (w : Fin n → (Fin N → ℝ) × (Fin N → ℝ)) :=
  (z₁ + ∑ i, (w i).1, z₂ + ∑ i, (w i).2)

lemma measurable_markPairEndpoint (n : ℕ) (z₁ z₂ : Fin N → ℝ) :
    Measurable (markPairEndpoint n z₁ z₂) := by
  exact (measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).fst)).prodMk
    (measurable_const.add (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).snd))

lemma markPairEndpoint_cons (n : ℕ) (z₁ z₂ a₁ a₂ : Fin N → ℝ)
    (w : Fin n → (Fin N → ℝ) × (Fin N → ℝ)) :
    markPairEndpoint (n+1) z₁ z₂ (Fin.cons (a₁,a₂) w) =
      markPairEndpoint n (z₁+a₁) (z₂+a₂) w := by
  simp only [markPairEndpoint,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,add_assoc]

lemma integral_markStateKernel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z : Fin N → ℝ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) :
    (∫ y, F y ∂markStateKernel κ z) = ∫ a, F (z+a) ∂κ z := by
  rw [markStateKernel_apply]
  exact integral_map (show AEMeasurable (fun a : Fin N → ℝ => z+a) (κ z) from
    (measurable_const.add measurable_id).aemeasurable) hF.aestronglyMeasurable

lemma integral_markStateParallel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z₁ z₂ : Fin N → ℝ)
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    (∫ y, F y ∂(markStateKernel κ ∥ₖ markStateKernel κ) (z₁,z₂)) =
      ∫ a₁, ∫ a₂, F (z₁+a₁,z₂+a₂) ∂κ z₂ ∂κ z₁ := by
  have h₁ : MeasurePreserving (fun a : Fin N → ℝ => z₁+a) (κ z₁) (markStateKernel κ z₁) :=
    ⟨measurable_const.add measurable_id,(markStateKernel_apply κ z₁).symm⟩
  have h₂ : MeasurePreserving (fun a : Fin N → ℝ => z₂+a) (κ z₂) (markStateKernel κ z₂) :=
    ⟨measurable_const.add measurable_id,(markStateKernel_apply κ z₂).symm⟩
  rw [Kernel.parallelComp_apply]
  rw [← (h₁.prod h₂).hasLaw.integral_comp hF.aestronglyMeasurable]
  apply integral_prod
  exact Integrable.of_bound (hF.comp ((measurable_const.add measurable_fst).prodMk
    (measurable_const.add measurable_snd))).aestronglyMeasurable C
    (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using
        hB (Prod.map (fun a => z₁+a) (fun a => z₂+a) p))

theorem markPairPathMean_independent_endpoint (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (z₁ z₂ : Fin N → ℝ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    markPairPathMean n κ 0 z₁ z₂ (fun w => F (markPairEndpoint n z₁ z₂ w)) =
      ∫ y, F y ∂(markTailEndpointKernel n κ ∥ₖ markTailEndpointKernel n κ) (z₁,z₂) := by
  induction n generalizing κ z₁ z₂ with
  | zero => simp [markPairPathMean,markPairEndpoint,markTailEndpointKernel,Kernel.id_apply]
  | succ n ih =>
    let η := markTailEndpointKernel n (fun i => κ (i+1))
    have hI : Integrable F (((η ∥ₖ η) ∘ₖ
        (markStateKernel (κ 0) ∥ₖ markStateKernel (κ 0))) (z₁,z₂)) :=
      Integrable.of_bound hF.aestronglyMeasurable C
        (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p)
    have hH : Measurable (fun p => ∫ y, F y ∂(η ∥ₖ η) p) :=
      hF.stronglyMeasurable.integral_kernel.measurable
    have hHB : ∀ p, |∫ y, F y ∂(η ∥ₖ η) p| ≤ C := by
      intro p
      simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
        (norm_integral_le_of_norm_le_const (f := F) (C := C) (μ := (η ∥ₖ η) p)
          (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hB y))
    rw [markTailEndpointKernel,← Kernel.parallelComp_comp_parallelComp,
      Kernel.integral_comp hI,integral_markStateParallel (κ 0) z₁ z₂ _ hH hHB]
    simp only [markPairPathMean]
    apply integral_congr_ae
    apply ae_of_all
    intro a₁
    apply integral_congr_ae
    apply ae_of_all
    intro a₂
    simp only [markPairEndpoint_cons]
    exact ih (fun i => κ (i+1)) (z₁+a₁) (z₂+a₂)

theorem markPairPathMean_shared_endpoint (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (d : Fin (n+1)) (z : Fin N → ℝ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ y, |F y| ≤ C) :
    markPairPathMean n κ d.val z z (fun w => F (markPairEndpoint n z z w)) =
      ∫ y, F y ∂markPairEndpointKernel n κ d z := by
  induction n generalizing κ z with
  | zero => simp [markPairPathMean,markPairEndpoint,markPairEndpointKernel,
      Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod_dirac]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · simpa only [Fin.val_zero,markPairEndpointKernel,Fin.cases_zero,Kernel.prod_apply,
        Kernel.parallelComp_apply] using
        markPairPathMean_independent_endpoint (n+1) κ z z F hF hB
    · let η := markPairEndpointKernel n (fun i => κ (i+1)) j
      have hI : Integrable F ((η ∘ₖ markStateKernel (κ 0)) z) :=
        Integrable.of_bound hF.aestronglyMeasurable C
          (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p)
      have hH : Measurable (fun p => ∫ y, F y ∂η p) :=
        hF.stronglyMeasurable.integral_kernel.measurable
      simp only [markPairEndpointKernel,Fin.cases_succ,Fin.val_succ]
      rw [Kernel.integral_comp hI,integral_markStateKernel (κ 0) z _ hH]
      simp only [markPairPathMean]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      simp only [markPairEndpoint_cons]
      exact ih (fun i => κ (i+1)) j (z+a)

end InvariantIsing

end

end OAI
