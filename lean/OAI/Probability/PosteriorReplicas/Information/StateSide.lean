import OAI.Probability.PosteriorReplicas.Information.StateExperiment

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def stateSideKernel {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) :
    Kernel (Fin V) (Data d ℓ × (Vec d × Fin W)) :=
  Kernel.ofFunOfCountable (fun v => randomSideLaw (haarRows d ℓ)
    (fun z => labels z.1 z.2) (stateOutputKernel q κ v))

instance {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateSideKernel ℓ q κ) where
  isProbabilityMeasure v := by
    change IsProbabilityMeasure ((haarRows d ℓ).prod (stateOutputKernel q κ v) |>.map
      (fun z => ((z.1,labels z.1 z.2.1),z.2)))
    infer_instance

lemma stateSideKernel_apply {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    stateSideKernel ℓ q κ v = randomSideLaw (haarRows d ℓ)
      (fun z => labels z.1 z.2) (stateOutputKernel q κ v) := rfl

lemma stateHaarSideLaw_eq_compProd {d ℓ k V W : ℕ}
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    stateHaarSideLaw ℓ (stateMessageLaw q κ) =
      (q.snd ⊗ₘ stateSideKernel ℓ q κ).map
        (MeasurableEquiv.prodAssoc.symm :
          Fin V × (Data d ℓ × (Vec d × Fin W)) ≃ᵐ
            (Fin V × Data d ℓ) × (Vec d × Fin W)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  let F : Rows d ℓ × Fin V → ℝ≥0∞ := fun z =>
    ∫⁻ sw, g ((z.2,(z.1,labels z.1 sw.1)),sw) ∂stateOutputKernel q κ z.2
  have hF : Measurable F := by
    exact (show Measurable (fun z : (Rows d ℓ × Fin V) × (Vec d × Fin W) =>
      g ((z.1.2,(z.1.1,labels z.1.1 z.2.1)),z.2)) by unfold labels; fun_prop).lintegral_kernel_prod_right'
      (κ := (stateOutputKernel q κ).comap Prod.snd measurable_snd)
  rw [stateHaarSideLaw,lintegral_map hg (by unfold labels; fun_prop),
    lintegral_prod _ (by unfold labels; fun_prop),
    lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  calc
    _ = ∫⁻ B, ∫⁻ v, F (B,v) ∂q.snd ∂haarRows d ℓ := by
      apply lintegral_congr
      intro B
      rw [stateMessageLaw_eq_compProd,lintegral_map (by unfold labels; fun_prop) (by fun_prop),
        Measure.lintegral_compProd (by unfold labels; fun_prop)]
    _ = ∫⁻ v, ∫⁻ B, F (B,v) ∂haarRows d ℓ ∂q.snd :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      rw [stateSideKernel_apply,randomSideLaw,lintegral_map (by fun_prop) (by unfold labels; fun_prop),
        lintegral_prod _ (by unfold labels; fun_prop)]
      rfl

lemma stateHaarInformation_average {d ℓ k V W : ℕ} [NeZero W]
    (hℓ : ℓ ≤ d) (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    cmi (stateHaarSideLaw ℓ (stateMessageLaw q κ)) =
      ∑ v, q.snd {v} * conditionalInformation (sideLaw ℓ (stateOutputKernel q κ v)) := by
  simp only [stateHaarSideLaw_eq_compProd]
  rw [cmi_compProd_assoc,lintegral_fintype]
  apply Finset.sum_congr rfl
  intro v _
  simp only [stateSideKernel_apply,cmi_haar_eq_gaussian hℓ,mul_comm]

end PosteriorReplicas
end

end OAI
