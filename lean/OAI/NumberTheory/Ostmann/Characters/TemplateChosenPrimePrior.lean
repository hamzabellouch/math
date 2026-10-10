import OAI.NumberTheory.Ostmann.Characters.ProductPriorSplit
import OAI.NumberTheory.Ostmann.Characters.TemplateChosenPrime

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem constituentPrimePrior_chosen_mean (k j:ℕ) (width:Role→ℕ) (hw:0<width .word) {Q:ℕ}
    (E:(schedule k j).Constituent width→Finset (PrimeUpTo Q))
    (hE:∀i,0<primeShellMass (E i)) (F:((schedule k j).Constituent width→PrimeUpTo Q)→ℝ) :
    (constituentPrimePrior (schedule k j) width E hE).mean F =
      (productPrior (fun i:RemainingPrime k j width=>primeShellPrior (E i.val) (hE i.val))).mean
        (fun y=>(productPrior (fun w:WordSlot k j=>
          primeShellPrior (E (chosenPrimeIndex k j width hw w)) (hE _))).mean
            (fun z=>F (assembleChosen k j width y z))) := by
  have hs (y : RemainingPrime k j width → PrimeUpTo Q)
      (z : WordSlot k j → PrimeUpTo Q) :
      splitPriorSample (chosenPrimeSplit k j width hw) y z = assembleChosen k j width y z := by
    funext i
    unfold splitPriorSample assembleChosen
    change Sum.elim z y (if h:IsChosen k j width i then .inl ⟨i.1,h.1,h.2.1⟩ else .inr ⟨i,h⟩)=_
    split_ifs <;> rfl
  have h := productPrior_split_mean (chosenPrimeSplit k j width hw)
    (fun i=>primeShellPrior (E i) (hE i)) F
  simp_rw [hs] at h
  simpa only [constituentPrimePrior,chosenPrimeSplit,Equiv.coe_fn_mk] using h

end Ostmann.Characters.Template

end

end OAI
