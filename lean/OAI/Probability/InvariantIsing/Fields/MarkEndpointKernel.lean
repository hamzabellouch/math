import OAI.Probability.InvariantIsing.Fields.MarkPairRecursion
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace OAI

/-! Endpoint kernels of the finite ancestor-dependent increment chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing
variable {N : ℕ}

def markStateKernel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ)) :
    Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  (Kernel.id ×ₖ κ).map (fun p => p.1+p.2)

instance markStateKernel_markov (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] : IsMarkovKernel (markStateKernel κ) := by
  unfold markStateKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.add measurable_snd)

lemma markStateKernel_apply (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] (z : Fin N → ℝ) :
    markStateKernel κ z = (κ z).map (fun a => z+a) := by
  rw [markStateKernel,Kernel.map_apply _ (show Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1+p.2) from
    measurable_fst.add measurable_snd), Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  rw [Measure.map_map (show Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1+p.2) from
    measurable_fst.add measurable_snd) measurable_prodMk_left]
  rfl

def markTailEndpointKernel : ℕ → (ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) →
    Kernel (Fin N → ℝ) (Fin N → ℝ)
  | 0, _ => Kernel.id
  | n+1, κ => markTailEndpointKernel n (fun i => κ (i+1)) ∘ₖ markStateKernel (κ 0)

instance markTailEndpointKernel_markov (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (markTailEndpointKernel n κ) := by
  induction n generalizing κ with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    let := ih (fun i => κ (i+1))
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

def markPairEndpointKernel : (n : ℕ) → (ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) →
    Fin (n+1) → Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | 0, _, _ => Kernel.id ×ₖ Kernel.id
  | n+1, κ, d => Fin.cases (markTailEndpointKernel (n+1) κ ×ₖ markTailEndpointKernel (n+1) κ)
      (fun j => markPairEndpointKernel n (fun i => κ (i+1)) j ∘ₖ markStateKernel (κ 0)) d

instance markPairEndpointKernel_markov (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (d : Fin (n+1)) : IsMarkovKernel (markPairEndpointKernel n κ d) := by
  induction n generalizing κ with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.id ×ₖ Kernel.id))
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · change IsMarkovKernel (_ ×ₖ _)
      infer_instance
    · let := ih (fun i => κ (i+1)) j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

end InvariantIsing

end

end OAI
