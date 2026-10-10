import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeInteger
import OAI.NumberTheory.Ostmann.Characters.TemplateWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure Arithmetic
attribute [local instance] Classical.propDecidable

theorem actual_prime_weight_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K R N:ℕ,∀ [NeZero R],∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀p,0<primeShellMass (E p),
      ∀ L:List Bool→J→ℕ,(∀p j,R^(K+2)≤L p j)→
      (∀p q,q∈E p→∃j,L p j≤q.val ∧ q.val≤2*L p j)→
      (∀p q,q∈E p→q.val.Coprime (R^(K+2)))→
      ∀ d:List Bool→Data R,∀ j:ℕ,j≤K→∀ p,∀ C C':State k j,
      ∀ mask:(l:ℕ)→ℤ→State k l→Prop,∀ X Δ W:ℝ,0<X→
      ∀ s:ℤ,∀ t:HistoryReconstruction.Tree j,
      BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>if IntegerSupport k R d j p
          (installWords k j C (chosenPrimeWords k j x))
          (installWords k j C' (chosenPrimeWords k j x)) then
          ‖weight k mask X Δ W j s (installWords k j C (chosenPrimeWords k j x)) t‖^2 else 0) ≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)*
      ((BinaryPriorExposure.cost
        (fun p=>primeResidueCost (Q:=R^(K+2)) (J:=J) (E p) (hE p)) j p:ℝ)*
        ((budget A ε (fun p=>ambientData K R (d p)) j p).value:ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := actual_prime_integer_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K R N _ J _ E hE L hL hcover hcop d j hj p C C' mask X Δ W hX s t
  let B := (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^j)*2)
  calc
    _ ≤ BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>B*(if IntegerSupport k R d j p
          (installWords k j C (chosenPrimeWords k j x))
          (installWords k j C' (chosenPrimeWords k j x)) then 1 else 0)) := by
      apply BinaryPriorExposure.mean_mono
      intro x
      split_ifs
      · simpa only [mul_one] using weight_norm_sq_le k mask X Δ W hX j s _ t
      · simp only [mul_zero,le_refl]
    _ = B*BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>if IntegerSupport k R d j p
          (installWords k j C (chosenPrimeWords k j x))
          (installWords k j C' (chosenPrimeWords k j x)) then 1 else 0) :=
      BinaryPriorExposure.mean_const_mul _ _ _ _ B
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hbound k K R N J E hE L hL hcover hcop d j hj p C C')
        (pow_nonneg (mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le) _)

end Ostmann.Characters.Template

end

end OAI
