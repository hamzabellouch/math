import OAI.NumberTheory.Ostmann.Characters.BinaryPriorSum
import OAI.NumberTheory.Ostmann.Characters.PrimeResidueCost
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryWeightBound

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure Arithmetic
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem reduced_literalWeight_nonneg (ε:ℝ) (A:NNReal) (j:ℕ) (p:List Bool)
    (s:ℤ) (t:HistoryReconstruction.Tree j) :
    0≤literalWeight (ReducedFrequencyTree.factor ε A) j p s t := by
  induction j generalizing p s with
  | zero => exact zero_le_one
  | succ j ih =>
    exact mul_nonneg (mul_nonneg (mul_nonneg A.property
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (ih _ _ _)) (ih _ _ _)

theorem actual_history_square_sum_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K j:ℕ,j≤K→∀ p,
      ∀ S:List Bool→Finset ℤ,(∀q z,z∈S q→z≠0)→
      ∀ N:ℕ,∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀q,0<primeShellMass (E q),
      ∀ L:SupportedHistory S j p→List Bool→J→ℕ,
      (∀h q i,(modulus j p h.val.1 h.val.2)^(K+2)≤L h q i)→
      (∀h q z,z∈E q→∃i,L h q i≤z.val ∧ z.val≤2*L h q i)→
      (∀(h:SupportedHistory S j p) q z,z∈E q→z.val.Coprime ((modulus j p h.val.1 h.val.2)^(K+2)))→
      ∀ C:State k j,∀ mask:(l:ℕ)→ℤ→State k l→Prop,∀ X Δ W:ℝ,0<X→
      BinaryPriorExposure.mean (fun q=>primeShellPrior (E q) (hE q)) j p
        (fun x=>∑h:SupportedHistory S j p,
          if UnitSupported k j h.val.1 (installWords k j C (chosenPrimeWords k j x)) h.val.2 then
            ‖weight k mask X Δ W j h.val.1
              (installWords k j C (chosenPrimeWords k j x)) h.val.2‖^2 else 0) ≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)*
      ((BinaryPriorExposure.cost (fun q=>shellResidueCost (J:=J) (E q) (hE q)) j p:ℝ)*
        historyTotal S (ReducedFrequencyTree.factor ε A) j p) := by
  obtain ⟨A,hA,hbound⟩ := actual_history_weight_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K j hj p S hS N J _ E hE L hL hcover hcop C mask X Δ W hX
  let B := (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)
  have hB : 0≤B := pow_nonneg (mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le) _
  rw [BinaryPriorExposure.mean_sum]
  calc
    _ ≤ ∑h:SupportedHistory S j p,
        B*((BinaryPriorExposure.cost (fun q=>shellResidueCost (J:=J) (E q) (hE q)) j p:ℝ)*
          literalWeight (ReducedFrequencyTree.factor ε A) j p h.val.1 h.val.2) := by
      apply Finset.sum_le_sum
      intro h hh
      let : NeZero (modulus j p h.val.1 h.val.2) := ⟨(modulus_pos S hS h.property).ne'⟩
      refine (hbound k K j hj p h.val.1 h.val.2 S hS h.property N J E hE
        (L h) (hL h) (hcover h) (hcop h) C mask X Δ W hX).trans ?_
      apply mul_le_mul_of_nonneg_left _ hB
      apply mul_le_mul_of_nonneg_right _ (reduced_literalWeight_nonneg ε A j p _ _)
      exact_mod_cast binary_cost_mono _ _ (fun q=>primeResidueCost_le_shell (Q:=(modulus j p h.val.1 h.val.2)^(K+2))
        (J:=J) (E q) (hE q)) j p
    _ = _ := by
      simp only [B,historyTotal,Finset.mul_sum]

end Ostmann.Characters.Template

end

end OAI
