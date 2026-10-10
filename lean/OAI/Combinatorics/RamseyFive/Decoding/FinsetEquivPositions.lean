import Mathlib

namespace OAI

namespace SharpRamseyFive
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
def equivPositions (e : A≃B) (S : Finset A) : Finset B := S.map e.toEmbedding
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
lemma mem_equivPositions (e : A≃B) (S : Finset A) (i : B) :
    i∈equivPositions e S ↔ e.symm i∈S := by
  simp [equivPositions]
lemma equivPositions_compl_card (e : A≃B) (S : Finset A) :
    (equivPositions e S)ᶜ.card=Sᶜ.card := by
  rw [Finset.card_compl,Finset.card_compl]
  simp only [equivPositions,Finset.card_map,Fintype.card_congr e]
end
end SharpRamseyFive

end OAI
