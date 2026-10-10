import OAI.NumberTheory.TwoPoint.Walks.WitnessSystemCodes
import OAI.NumberTheory.TwoPoint.Bounds.OrderedPrimeSystems
import OAI.NumberTheory.TwoPoint.Walks.WordRelations

namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations

structure PackedPrimeRelation (ι : Type*) where
  Term : Type
  [termFintype : Fintype Term]
  monomial : Term → PrimeMonomial ι

attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]

abbrev selected (d : WitnessSystemData n N ι) (i : d.chosen) : ι := (d.slot i).1
abbrev control (d : WitnessSystemData n N ι) (i : d.chosen) : ι := (d.slot i).2.1
abbrev partner (d : WitnessSystemData n N ι) (i : d.chosen) : Fin n := (d.slot i).2.2.1
abbrev left (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.1
abbrev right (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.1
abbrev departure (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.2.1
abbrev partnerDeparture (d : WitnessSystemData n N ι) (i : d.chosen) : Fin (N + 1) := (d.slot i).2.2.2.2.2.2

/-- Modes zero and one use internal intervals. Modes two and three
use the earlier and later comparison, respectively. -/
def relation (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (i : d.chosen) : PackedPrimeRelation ι :=
  if d.mode.val < 2 then {
    Term := Fin (word i).word.length
    termFintype := inferInstance
    monomial := (word i).intervalRelation h (d.left i) (d.right i) }
  else if d.mode.val = 2 then {
    Term := Fin main.word.length ⊕ (Fin (word i).word.length ⊕ Fin (word (d.partner i)).word.length)
    termFintype := inferInstance
    monomial := comparisonRelation main (word i) (word (d.partner i)) h
      (d.left i) (d.right i) (d.departure i) (d.partnerDeparture i) }
  else {
    Term := Fin main.word.length ⊕ (Fin (word (d.partner i)).word.length ⊕ Fin (word i).word.length)
    termFintype := inferInstance
    monomial := comparisonRelation main (word (d.partner i)) (word i) h
      (d.left i) (d.right i) (d.partnerDeparture i) (d.departure i) }

@[instance_reducible] noncomputable def chosenOrder (d : WitnessSystemData n N ι) : LinearOrder d.chosen :=
  if d.mode.val % 2 = 0 then inferInstance
  else (inferInstance : LinearOrder (OrderDual d.chosen))

/-- This is a support property of the decoded expressions, independent of
all numerical values assigned to the prime labels. -/
def Triangular (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) : Prop :=
  (∀ i, d.control i ≠ d.selected i) ∧
    ∀ i j, @LT.lt d.chosen d.chosenOrder.toLT i j →
      d.selected j ∉ primeRelationSupport (d.relation main word h i).monomial ∧
        d.control i ≠ d.selected j

def Holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (x : ι → ℤ) : Prop :=
  ∀ i, primeRelationEvent (d.relation main word h i).monomial (d.selected i) (d.control i) x

noncomputable def toSystem (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    OrderedPrimeSystem ι where
  Index := d.chosen
  indexFintype := inferInstance
  indexOrder := d.chosenOrder
  Term i := (d.relation main word h i).Term
  termFintype i := (d.relation main word h i).termFintype
  relation i := (d.relation main word h i).monomial
  selected := d.selected
  control := d.control
  control_ne := ht.1
  triangular := ht.2

@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI
