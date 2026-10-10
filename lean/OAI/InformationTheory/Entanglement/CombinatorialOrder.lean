import OAI.InformationTheory.Entanglement.CombinatorialQuestions
import OAI.InformationTheory.Entanglement.ParityData

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction

instance baseLinearOrder : LinearOrder Base := LinearOrder.lift'
  (fun A => A.val.sort (· ≤ ·)) (by
    intro A B h
    apply Subtype.ext
    have he := congrArg List.toFinset h
    simpa only [Finset.sort_toFinset] using he)
instance (priority := 2000) baseLE : LE Base := baseLinearOrder.toLE
instance (priority := 2000) baseLT : LT Base := baseLinearOrder.toLT

instance questionLinearOrder : LinearOrder Question := LinearOrder.lift'
  (fun q => [q.1,q.2.1,q.2.2]) (by
    intro q r h
    simp only [List.cons.injEq,and_true] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2))

instance (priority := 2000) questionLE : LE Question := questionLinearOrder.toLE
instance (priority := 2000) questionLT : LT Question := questionLinearOrder.toLT
abbrev Eight := {S : Finset Question // S.card=8}
instance eightLinearOrder : LinearOrder Eight := LinearOrder.lift'
  (fun S => S.val.sort (· ≤ ·)) (by
    intro S T h
    apply Subtype.ext
    have he := congrArg List.toFinset h
    simpa only [Finset.sort_toFinset] using he)
instance (priority := 2000) eightLE : LE Eight := eightLinearOrder.toLE
instance (priority := 2000) eightLT : LT Eight := eightLinearOrder.toLT
lemma eight_card : Fintype.card Eight=L := by
  rw [L_def,Fintype.card_finset_len,question_card]

def six (S : Eight) (t : Fin 6) : Question :=
  S.val.orderEmbOfFin S.property (Fin.castLE (by decide) t)
lemma six_mem (S : Eight) (t : Fin 6) : six S t ∈ S.val :=
  S.val.orderEmbOfFin_mem S.property _
lemma six_injective (S : Eight) : Function.Injective (six S) :=
  (S.val.orderEmbOfFin S.property).injective.comp (Fin.castLE_injective (by decide))

def OrthogonalEight (S : Eight) : Prop :=
  Clique (fun q r => ProjectionCriterion.correlation u q r=0) S.val

def contextAt (S : Eight) (q : Question) : Option (Fin 6) := by
  classical
  exact if OrthogonalEight S then
    if h : ∃ t, six S t=q then some (Classical.choose h) else none
  else none
lemma contextAt_six (S : Eight) (hS : OrthogonalEight S) (t : Fin 6) :
    contextAt S (six S t)=some t := by
  unfold contextAt
  rw [ite_eq_left hS,dite_eq_left (show ∃ t', six S t'=six S t from ⟨t,rfl⟩)]
  congr 1
  exact six_injective S (Classical.choose_spec (show ∃ t', six S t'=six S t from ⟨t,rfl⟩))
lemma contextAt_some (S : Eight) (q : Question) (t : Fin 6)
    (ht : contextAt S q=some t) : OrthogonalEight S ∧ six S t=q := by
  unfold contextAt at ht
  split_ifs at ht with ho he
  · have heq := Option.some.inj ht
    refine ⟨ho,?_⟩
    rw [← heq]
    exact Classical.choose_spec he

abbrev OutputCoordinate := Eight → Four
abbrev Label := Question × (Eight → Outcome)
lemma four_card : Fintype.card Four=4 := rfl
lemma outcome_card : Fintype.card Outcome=4 := rfl
attribute [local irreducible] L Q b
lemma card_arrow_eq {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    {a b : ℕ} (ha : Fintype.card α=a) (hb : Fintype.card β=b) :
    Fintype.card (α → β)=b^a := by rw [Fintype.card_fun,ha,hb]
lemma card_pair_eq {α β : Type} [Fintype α] [Fintype β]
    {a b : ℕ} (ha : Fintype.card α=a) (hb : Fintype.card β=b) :
    Fintype.card (α × β)=a*b := by rw [Fintype.card_prod,ha,hb]
lemma output_card : Fintype.card OutputCoordinate=D := by
  have he := card_arrow_eq eight_card four_card
  exact he
lemma outcomeString_card : Fintype.card (Eight → Outcome)=D := by
  have he := card_arrow_eq eight_card outcome_card
  exact he
lemma label_card : Fintype.card Label=m := by
  have he := card_pair_eq question_card outcomeString_card
  exact he

instance fourLinearOrder : LinearOrder Four :=
  LinearOrder.lift' (toLex : Four ≃ Lex Four) toLex.injective
instance (priority := 2000) fourLE : LE Four := fourLinearOrder.toLE
instance (priority := 2000) fourLT : LT Four := fourLinearOrder.toLT
instance eightWellFounded : @WellFoundedLT Eight eightLinearOrder.toLT :=
  @Finite.to_wellFoundedLT Eight inferInstance eightLinearOrder.toPreorder

instance outputLinearOrder : LinearOrder OutputCoordinate :=
  LinearOrder.lift' (toLex : OutputCoordinate ≃ Lex OutputCoordinate) toLex.injective
instance labelLinearOrder : LinearOrder Label :=
  LinearOrder.lift' (toLex : Label ≃ Lex Label) toLex.injective

def orderedEnumeration {τ : Type} [Fintype τ] [LinearOrder τ] {n : ℕ}
    (hc : Fintype.card τ=n) : Fin n ≃ τ :=
  ((Finset.univ : Finset τ).orderIsoOfFin (by simpa using hc)).toEquiv.trans
    { toFun := Subtype.val
      invFun := fun x => ⟨x,Finset.mem_univ x⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => rfl }
def outputEnumeration : Fin D ≃ OutputCoordinate := orderedEnumeration output_card
def labelEnumeration : Fin m ≃ Label := orderedEnumeration label_card

end FiniteConstruction

end

end OAI
