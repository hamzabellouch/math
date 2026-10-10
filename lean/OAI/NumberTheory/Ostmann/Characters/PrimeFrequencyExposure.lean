import OAI.NumberTheory.Ostmann.Characters.BinaryPriorExposure
import OAI.NumberTheory.Ostmann.Characters.FrequencyExposureLeaves
import OAI.NumberTheory.Ostmann.Characters.PrimeResiduePrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction Preliminaries BinaryExposure FrequencyExposure
attribute [local instance] Classical.propDecidable

def primeResidueCost {N Q:ℕ} [NeZero Q] {J:Type*} [Fintype J]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E) : NNReal :=
  ⟨3*Fintype.card J*(Fintype.card (ZMod Q)ˣ:ℝ)/((Q:ℝ)*primeShellMass E),by positivity⟩

theorem paired_prime_leaf_bound (ε:ℝ) (hε:0<ε) :
    ∃ C:NNReal, 0<C ∧ ∀ N Q:ℕ, ∀ [NeZero Q], ∀ J:Type*, ∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N), ∀ hE:∀p,0<primeShellMass (E p),
      ∀ L:List Bool→J→ℕ, (∀p j,Q≤L p j) →
      (∀p q,q∈E p→∃j,L p j≤q.val ∧ q.val≤2*L p j) →
      (∀p q,q∈E p→q.val.Coprime Q) →
      ∀ H:Type*, ∀ d:List Bool→Data Q, ∀ a:∀p,Coefficients H (d p),
      ∀ left right:List Bool→H→(ZMod Q)ˣ→(ZMod Q)ˣ→H,
      ∀ k p h,
      BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) k p
        (fun x=>if leafAdmissible (constraint d a) (update false left) (update true right) k (p,h)
          (BinaryPriorExposure.map (fun _=>primeUnitResidue Q) k p x) then 1 else 0) ≤
      (BinaryPriorExposure.cost (fun p=>primeResidueCost (Q:=Q) (J:=J) (E p) (hE p)) k p:ℝ)*
        ((budget C ε d k p).value:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := paired_frequency_leaf_count ε hε
  refine ⟨C,hC,?_⟩
  intro N Q _ J _ E hE L hL hcover hcop H d a left right k p h
  let D : List Bool→NNReal := fun p=>primeResidueCost (Q:=Q) (J:=J) (E p) (hE p)
  have hf (p:List Bool) (b:(ZMod Q)ˣ) :
      (pushForwardPrior (primeShellPrior (E p) (hE p)) (primeUnitResidue Q)).mass b≤
        (D p:ℝ)/(Fintype.card (ZMod Q)ˣ:ℝ) :=
    primeShellPrior_unit_domination (E p) (hE p) (L p) (hL p) (hcover p) (hcop p) b
  have ht := BinaryPriorExposure.indicator_le_uniform
    (fun p=>primeShellPrior (E p) (hE p)) (fun _=>primeUnitResidue Q) D hf k p
    (leafAdmissible (constraint d a) (update false left) (update true right) k (p,h))
  exact ht.trans (mul_le_mul_of_nonneg_left (hbound Q H d a left right k p h)
    (BinaryPriorExposure.cost D k p).property)

end Ostmann.Characters

end

end OAI
