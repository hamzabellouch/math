import OAI.NumberTheory.Ostmann.Characters.TemplateHistorySquareSum
import OAI.NumberTheory.Ostmann.Characters.TemplateRetainedNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure Arithmetic
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem actual_retained_square_sum_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K j:ℕ,j≤K→∀ p,
      ∀ S:List Bool→Finset ℤ,(∀q z,z∈S q→z≠0)→
      ∀ N:ℕ,∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀q,0<primeShellMass (E q),
      ∀ L:SupportedHistory S j p→List Bool→J→ℕ,
      (∀h q i,(modulus j p h.val.1 h.val.2)^(K+2)≤L h q i)→
      (∀h q z,z∈E q→∃i,L h q i≤z.val ∧ z.val≤2*L h q i)→
      (∀(h:SupportedHistory S j p) q z,z∈E q→z.val.Coprime ((modulus j p h.val.1 h.val.2)^(K+2)))→
      ∀ C:State k j,∀ B V:(l:ℕ)→State k (l+1)→ℤ,
      ∀ extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop,∀ mask:(l:ℕ)→ℤ→State k l→Prop,∀ X Δ W:ℝ,0<X→
      BinaryPriorExposure.mean (fun q=>primeShellPrior (E q) (hE q)) j p
        (fun x=>∑h:SupportedHistory S j p,
          ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1
            (installWords k j C (chosenPrimeWords k j x)) h.val.2‖^2) ≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)*
      ((BinaryPriorExposure.cost (fun q=>shellResidueCost (J:=J) (E q) (hE q)) j p:ℝ)*
        historyTotal S (ReducedFrequencyTree.factor ε A) j p) := by
  obtain ⟨A,hA,hbound⟩ := actual_history_square_sum_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K j hj p S hS N J _ E hE L hL hcover hcop C B V extra mask X Δ W hX
  refine le_trans ?_ (hbound k K j hj p S hS N J E hE L hL hcover hcop C mask X Δ W hX)
  apply BinaryPriorExposure.mean_mono
  intro x
  exact Finset.sum_le_sum (fun h _=>retainedHistoryWeight_sq_le_supported k j B V extra mask X Δ W
    h.val.1 (installWords k j C (chosenPrimeWords k j x)) h.val.2)

end Ostmann.Characters.Template

end

end OAI
