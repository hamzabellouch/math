import OAI.NumberTheory.Ostmann.Characters.TemplateIntegerSupport
import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeArithmetic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure
attribute [local instance] Classical.propDecidable

def contextOfState (k R j:ℕ) (C:State k j) : KnownStates k R :=
  Function.update (fun _ _=>0) j (fun i=>(C i:ZMod (R^(j+2))))

theorem contextOfState_matches (k R j:ℕ) (C:State k j) :
    ContextMatches k R j (contextOfState k R j C) C := by
  intro i
  simp only [contextOfState,Function.update_self]

theorem actual_prime_integer_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K R N:ℕ,∀ [NeZero R],∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀p,0<primeShellMass (E p),
      ∀ L:List Bool→J→ℕ,(∀p j,R^(K+2)≤L p j)→
      (∀p q,q∈E p→∃j,L p j≤q.val ∧ q.val≤2*L p j)→
      (∀p q,q∈E p→q.val.Coprime (R^(K+2)))→
      ∀ d:List Bool→Data R,∀ j:ℕ,j≤K→∀ p,∀ C C':State k j,
      BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>if IntegerSupport k R d j p
          (installWords k j C (chosenPrimeWords k j x))
          (installWords k j C' (chosenPrimeWords k j x)) then 1 else 0) ≤
      (BinaryPriorExposure.cost
        (fun p=>primeResidueCost (Q:=R^(K+2)) (J:=J) (E p) (hE p)) j p:ℝ)*
        ((budget A ε (fun p=>ambientData K R (d p)) j p).value:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := actual_prime_arithmetic_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K R N _ J _ E hE L hL hcover hcop d j hj p C C'
  refine le_trans ?_ (hbound k K R N J E hE L hL hcover hcop d j hj p
    (contextOfState k R j C,contextOfState k R j C') C C'
    (contextOfState_matches k R j C) (contextOfState_matches k R j C'))
  apply BinaryPriorExposure.mean_mono
  intro x
  by_cases hs:IntegerSupport k R d j p
      (installWords k j C (chosenPrimeWords k j x))
      (installWords k j C' (chosenPrimeWords k j x))
  · have he := integerSupport_implies_arithmeticSupport k R d j p C C' _ hs
    simp only [ite_eq_left hs,ite_eq_left he,le_refl]
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

end Ostmann.Characters.Template

end

end OAI
