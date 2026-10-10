import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateUnitSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure Arithmetic
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem actual_history_weight_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K j:ℕ,j≤K→∀ p s (t:HistoryReconstruction.Tree j),
      ∀ S:List Bool→Finset ℤ,∀ hS:(∀q z,z∈S q→z≠0),∀ hs:RangeSupported S j p s t,
      let _ : NeZero (modulus j p s t) := ⟨(modulus_pos S hS hs).ne'⟩;
      ∀ N:ℕ,∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀q,0<primeShellMass (E q),
      ∀ L:List Bool→J→ℕ,(∀q i,(modulus j p s t)^(K+2)≤L q i)→
      (∀q z,z∈E q→∃i,L q i≤z.val ∧ z.val≤2*L q i)→
      (∀q z,z∈E q→z.val.Coprime ((modulus j p s t)^(K+2)))→
      ∀ C:State k j,∀ mask:(l:ℕ)→ℤ→State k l→Prop,∀ X Δ W:ℝ,0<X→
      BinaryPriorExposure.mean (fun q=>primeShellPrior (E q) (hE q)) j p
        (fun x=>if UnitSupported k j s (installWords k j C (chosenPrimeWords k j x)) t then
          ‖weight k mask X Δ W j s (installWords k j C (chosenPrimeWords k j x)) t‖^2 else 0) ≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)*
      ((BinaryPriorExposure.cost
        (fun q=>primeResidueCost (Q:=(modulus j p s t)^(K+2)) (J:=J) (E q) (hE q)) j p:ℝ)*
        literalWeight (ReducedFrequencyTree.factor ε A) j p s t) := by
  obtain ⟨A,hA,hbound⟩ := actual_prime_weight_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K j hj p s t S hS hs _ N J _ E hE L hL hcover hcop C mask X Δ W hX
  let : NeZero (modulus j p s t) := ⟨(modulus_pos S hS hs).ne'⟩
  have hb := hbound k K (modulus j p s t) N J E hE L hL hcover hcop
    (diagonalData j p s t) j hj p C C mask X Δ W hX s t
  simpa only [diagonal_integerSupport_iff,diagonal_ambient_budget_eq] using hb

end Ostmann.Characters.Template

end

end OAI
