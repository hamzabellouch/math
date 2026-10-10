import OAI.InformationTheory.Entanglement.CombinatorialNumbers

namespace OAI

noncomputable section
namespace FiniteConstruction

lemma function_card_eq_dimension {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (ha : Fintype.card α=L) (hb : Fintype.card β=4) :
    Fintype.card (α→β)=D := by
  unfold D
  rw [Fintype.card_fun,ha,hb]
end FiniteConstruction

end

end OAI
