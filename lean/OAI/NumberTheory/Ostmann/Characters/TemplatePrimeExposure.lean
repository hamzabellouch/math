import OAI.NumberTheory.Ostmann.Characters.PrimeFrequencyExposure
import OAI.NumberTheory.Ostmann.Characters.TemplateResidueExposure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure
attribute [local instance] Classical.propDecidable

theorem actual_prime_leaf_bound (ε:ℝ) (hε:0<ε) :
    ∃ C:NNReal, 0<C ∧ ∀ k K R N:ℕ, ∀ [NeZero R], ∀ J:Type*, ∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N), ∀ hE:∀p,0<primeShellMass (E p),
      ∀ L:List Bool→J→ℕ, (∀p j,R^(K+2)≤L p j) →
      (∀p q,q∈E p→∃j,L p j≤q.val ∧ q.val≤2*L p j) →
      (∀p q,q∈E p→q.val.Coprime (R^(K+2))) →
      ∀ d:List Bool→Data R, ∀ j p (h:PairedKnownStates k R),
      BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>if leafAdmissible (exposureConstraint k K R d)
          (exposureStep k K R d false) (exposureStep k K R d true) j (p,h)
          (BinaryPriorExposure.map (fun _=>primeUnitResidue (R^(K+2))) j p x) then 1 else 0) ≤
      (BinaryPriorExposure.cost
        (fun p=>primeResidueCost (Q:=R^(K+2)) (J:=J) (E p) (hE p)) j p:ℝ)*
        ((budget C ε (fun p=>ambientData K R (d p)) j p).value:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := actual_residue_leaf_count ε hε
  refine ⟨C,hC,?_⟩
  intro k K R N _ J _ E hE L hL hcover hcop d j p h
  let D : List Bool→NNReal := fun p=>primeResidueCost (Q:=R^(K+2)) (J:=J) (E p) (hE p)
  have hf (p:List Bool) (b:(ZMod (R^(K+2)))ˣ) :
      (pushForwardPrior (primeShellPrior (E p) (hE p)) (primeUnitResidue (R^(K+2)))).mass b≤
        (D p:ℝ)/(Fintype.card (ZMod (R^(K+2)))ˣ:ℝ) :=
    primeShellPrior_unit_domination (E p) (hE p) (L p) (hL p) (hcover p) (hcop p) b
  have ht := BinaryPriorExposure.indicator_le_uniform
    (fun p=>primeShellPrior (E p) (hE p)) (fun _=>primeUnitResidue (R^(K+2))) D hf j p
    (leafAdmissible (exposureConstraint k K R d)
      (exposureStep k K R d false) (exposureStep k K R d true) j (p,h))
  exact ht.trans (mul_le_mul_of_nonneg_left (hbound k K R d j p h)
    (BinaryPriorExposure.cost D j p).property)

end Ostmann.Characters.Template

end

end OAI
