import OAI.Probability.PosteriorReplicas.Information.FiniteConditionalEntropy
import OAI.Probability.PosteriorReplicas.Information.HaarInformationEq

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def initialStateKernel {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q] :
    Kernel (Fin V) (Vec d) := (q.map Prod.swap).condKernel

instance {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q] :
    IsMarkovKernel (initialStateKernel q) := by unfold initialStateKernel; infer_instance

lemma initialStateKernel_marginal {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q] :
    (q.snd ⊗ₘ initialStateKernel q).snd = q.fst := by
  have h : q.snd ⊗ₘ initialStateKernel q = q.map Prod.swap := by
    rw [initialStateKernel,← Measure.fst_map_swap (ρ := q),Measure.disintegrate]
  rw [h,Measure.snd_map_swap]

lemma lintegral_initialStateKernel {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    {g : Vec d × Fin V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂q = ∫⁻ v, ∫⁻ s, g (s,v) ∂initialStateKernel q v ∂q.snd := by
  have h : q.snd ⊗ₘ initialStateKernel q = q.map Prod.swap := by
    rw [initialStateKernel,← Measure.fst_map_swap (ρ := q),Measure.disintegrate]
  calc
    _ = ∫⁻ z, g z.swap ∂q.map Prod.swap := by
      rw [lintegral_map (by fun_prop) measurable_swap]
      rfl
    _ = _ := by rw [← h,Measure.lintegral_compProd (by fun_prop)]; rfl

def stateBlockKernel {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    Kernel (Data d k) (Fin W) := κ.comap (fun z => (v,z)) (by fun_prop)

instance {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] (v : Fin V) :
    IsMarkovKernel (stateBlockKernel κ v) := by unfold stateBlockKernel; infer_instance

def stateOutputKernel {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) : Kernel (Fin V) (Vec d × Fin W) :=
  Kernel.ofFunOfCountable (fun v => signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v))

instance {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateOutputKernel q κ) where
  isProbabilityMeasure v := inferInstanceAs
    (IsProbabilityMeasure (signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v)))

lemma stateOutputKernel_apply {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    stateOutputKernel q κ v = signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v) := rfl

lemma signalMessageLaw_lintegral {d k W : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin W)) [IsMarkovKernel κ]
    {g : Vec d × Fin W → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂signalMessageLaw p κ =
      ∫⁻ s, ∫⁻ A, ∫⁻ w, g (s,w) ∂κ (A,labels A s) ∂gaussianRows d k ∂p := by
  have hm : Measurable (fun a : Vec d × Rows d k =>
      ∫⁻ w, g (a.1,w) ∂messageKernel κ a) :=
    (hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
  rw [signalMessageLaw,lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  exact lintegral_prod _ hm.aemeasurable

lemma stateMessageLaw_lintegral {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ]
    {g : (Vec d × Fin V) × Fin W → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂stateMessageLaw q κ =
      ∫⁻ z, ∫⁻ A, ∫⁻ w, g (z,w) ∂κ (z.2,(A,labels A z.1)) ∂gaussianRows d k ∂q := by
  have hm : Measurable (fun a : (Vec d × Fin V) × Rows d k =>
      ∫⁻ w, g (a.1,w) ∂stateMessageKernel κ a) :=
    (hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
  rw [stateMessageLaw,lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  exact lintegral_prod _ hm.aemeasurable

lemma stateMessageLaw_eq_compProd {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    stateMessageLaw q κ = (q.snd ⊗ₘ stateOutputKernel q κ).map (fun z => ((z.2.1,z.1),z.2.2)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [stateMessageLaw_lintegral q κ hg,lintegral_map hg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop),lintegral_initialStateKernel q (show Measurable (fun z : Vec d × Fin V =>
      ∫⁻ A, ∫⁻ w, g (z,w) ∂κ (z.2,(A,labels A z.1)) ∂gaussianRows d k) from
      ((hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right' (κ := stateMessageKernel κ)).lintegral_prod_right)]
  apply lintegral_congr
  intro v
  rw [stateOutputKernel_apply,signalMessageLaw_lintegral _ _ (by fun_prop)]
  rfl

lemma stateMessageLaw_state_terminal {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    (stateMessageLaw q κ).map (fun z => (z.1.2,z.2)) = q.snd ⊗ₘ (stateOutputKernel q κ).snd := by
  rw [stateMessageLaw_eq_compProd,Measure.map_map (by fun_prop) (by fun_prop),
    Kernel.snd_eq,Measure.compProd_map measurable_snd]
  rfl

lemma stateMessageLaw_initial {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    (stateMessageLaw q κ).map (fun z => z.1.2) = q.snd := by
  rw [stateMessageLaw_eq_compProd,Measure.map_map (by fun_prop) (by fun_prop)]
  change (q.snd ⊗ₘ stateOutputKernel q κ).fst = q.snd
  exact Measure.fst_compProd _ _

lemma terminalConditionalEntropy_average {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    terminalConditionalEntropy (stateMessageLaw q κ) =
      ∑ v, q.snd.real {v} * finiteEntropy (stateOutputKernel q κ v).snd := by
  rw [terminalConditionalEntropy,stateMessageLaw_state_terminal,stateMessageLaw_initial,
    finiteEntropy_compProd_conditional]
  simp only [Kernel.snd_apply,Measure.snd]

end PosteriorReplicas
end

end OAI
