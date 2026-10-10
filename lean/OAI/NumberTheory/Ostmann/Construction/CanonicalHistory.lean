import OAI.NumberTheory.Ostmann.Construction.Coefficient
import OAI.NumberTheory.Ostmann.Construction.PrimeSources
import OAI.NumberTheory.Ostmann.Construction.TemplateReinsert

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

abbrev AllowedFrequency (V : ℕ → ℕ) (l : ℕ) :=
  ↥(Finset.Icc (-(V l : ℤ)) (V l : ℤ))

def HistoryChoices (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) : ℕ → Type
  | 0 => Unit
  | l+1 => AllowedFrequency V l × AllowedFrequency V l ×
      SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)) ×
      HistoryChoices sources seed V l × HistoryChoices sources seed V l

instance historyChoicesFintype (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → Fintype (HistoryChoices sources seed V l)
  | 0 => inferInstanceAs (Fintype Unit)
  | l+1 => by
    letI := historyChoicesFintype sources seed V l
    exact inferInstanceAs (Fintype (AllowedFrequency V l × AllowedFrequency V l ×
      SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)) ×
      HistoryChoices sources seed V l × HistoryChoices sources seed V l))

def decodedPivot (a : State) (v w : ℤ) (u hp hm : List SmallSlot) : ℕ :=
  (Arithmetic.reversalNumerator v w
    ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
    ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ) /
      (a.frequency*((u.map SmallSlot.value).prod:ℤ))).toNat

def decodeHistory (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → State → HistoryChoices sources seed V l → History l
  | 0, a, _ => .leaf a
  | l+1, a, c =>
    let T := Template.current seed l
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    let hp := a.small.take n
    let hm := a.small.drop n
    let p := decodedPivot a c.1.val c.2.1.val u hp hm
    let al : State := ⟨c.1.val,p,a.giantPlus,Template.reinsert (l+1) T u hp⟩
    let ar : State := ⟨c.2.1.val,p,a.giantMinus,Template.reinsert (l+1) T u hm⟩
    .node a p u hp hm
      (decodeHistory sources seed V l al c.2.2.2.1)
      (decodeHistory sources seed V l ar c.2.2.2.2)

@[simp] theorem decodeHistory_root (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) :
    (decodeHistory sources seed V l a c).root=a := by
  cases l <;> rfl

def choicesMass (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → HistoryChoices sources seed V l → ℝ
  | 0, _ => 1
  | l+1, c =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass c.2.2.1 *
      choicesMass sources seed V l c.2.2.2.1 * choicesMass sources seed V l c.2.2.2.2

theorem decodeHistory_internalMass (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) :
    (decodeHistory sources seed V l a c).internalMass (sourceMass sources)=
      choicesMass sources seed V l c := by
  induction l generalizing a with
  | zero => rfl
  | succ l ih =>
    simp only [decodeHistory, History.internalMass, assignedSlots_mass, ih, choicesMass]

def canonicalCoefficient (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) (l : ℕ) (a : State) : ℂ :=
  ∑ c : HistoryChoices sources seed V l,
    (choicesMass sources seed V l c:ℂ)*
      (decodeHistory sources seed V l a c).supportedWeight V outside base φ G

end Ostmann.Construction

end

end OAI
