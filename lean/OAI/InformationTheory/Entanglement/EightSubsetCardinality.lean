import OAI.InformationTheory.Entanglement.CombinatorialQuestions
import OAI.InformationTheory.Entanglement.ParityData

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction
abbrev EightTest := {S : Finset Question // S.card=8}
lemma eight_card_test : Fintype.card EightTest=L := by
  rw [Fintype.card_finset_len, question_card, L_def]
lemma d_refl : D=4^L := rfl
lemma big_card_test : Fintype.card (EightTest → Four) = D := by
  have hc : Fintype.card Four=4 := rfl
  rw [d_refl, Fintype.card_fun, hc, eight_card_test]
end FiniteConstruction

end

end OAI
