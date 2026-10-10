import OAI.NumberTheory.Ostmann.Construction.CanonicalEnumeration
import OAI.NumberTheory.Ostmann.Construction.HistorySupportSplit

namespace OAI

noncomputable section
namespace Ostmann.Construction

structure NodeFrame where
  state : State
  pivot : ℕ
  compensation : List SmallSlot
  plusSmall : List SmallSlot
  minusSmall : List SmallSlot
  plusState : State
  minusState : State

def canonicalFrame (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) : NodeFrame :=
  let T := Template.current seed l
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let n := (Template.remainder (l+1) T).length
  let hp := a.small.take n
  let hm := a.small.drop n
  let p := decodedPivot a v.val w.val us hp hm
  ⟨a,p,us,hp,hm,⟨v.val,p,a.giantPlus,Template.reinsert (l+1) T us hp⟩,
    ⟨w.val,p,a.giantMinus,Template.reinsert (l+1) T us hm⟩⟩

theorem decodeHistory_node (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (left right : HistoryChoices sources seed V l) :
    decodeHistory sources seed V (l+1) a (v,w,u,left,right) =
      let f := canonicalFrame sources seed V l a v w u
      History.node a f.pivot f.compensation f.plusSmall f.minusSmall
        (decodeHistory sources seed V l f.plusState left)
        (decodeHistory sources seed V l f.minusState right) := rfl

def NodeFrame.Valid (f : NodeFrame) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) : Prop :=
  History.rootConditions V outside (l+1) f.state ∧
    (Nat.Coprime f.state.giantPlus f.state.frequency.natAbs ∧
      Nat.Coprime f.state.giantMinus f.state.frequency.natAbs) ∧
    History.nodeRelations (l+1) f.state f.pivot f.compensation f.plusSmall f.minusSmall
      f.plusState f.minusState

def NodeFrame.scalar (f : NodeFrame) (φ : ℝ → ℝ) (G : ℝ) : ℂ :=
  ((f.compensation.map SmallSlot.value).prod:ℂ)*(φ (Real.log f.pivot-G):ℂ)

end Ostmann.Construction

end

end OAI
