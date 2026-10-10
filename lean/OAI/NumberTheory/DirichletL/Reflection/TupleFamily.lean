import OAI.NumberTheory.DirichletL.Reflection.Canonical
import OAI.NumberTheory.DirichletL.Descent.SlotProducts

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def tupleRepresentative (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : σ→Ideal Eis :=
  if h : ∃ p∈tuples, slotTupleProduct p=P then h.choose else hne.choose

omit [DecidableEq σ] in
lemma tupleRepresentative_mem (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : tupleRepresentative tuples hne P∈tuples := by
  unfold tupleRepresentative
  split
  next h => exact h.choose_spec.1
  next h => exact hne.choose_spec

omit [DecidableEq σ] in
lemma tupleRepresentative_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    slotTupleProduct (tupleRepresentative tuples hne P)=P := by
  have h : ∃ p∈tuples, slotTupleProduct p=P := Finset.mem_image.mp hP
  simp only [tupleRepresentative,dite_eq_left h]
  exact h.choose_spec.2

omit [DecidableEq σ] in
lemma tupleRepresentative_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    tupleRepresentative tuples hne (slotTupleProduct p)=p := by
  exact hinj (tupleRepresentative_mem tuples hne _) hp
    (tupleRepresentative_product tuples hne _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))

def tuplePrimeFamily (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) : PrimeFamily σ where
  ideal := tupleRepresentative tuples hne P
  maximal := hmax _ (tupleRepresentative_mem tuples hne P)
  good := hgood _ (tupleRepresentative_mem tuples hne P)

omit [DecidableEq σ] in
lemma tuplePrimeFamily_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis)
    (hP : P∈tuples.image slotTupleProduct) :
    (∏ i, (tuplePrimeFamily tuples hne hmax hgood P).ideal i)=P :=
  tupleRepresentative_product tuples hne P hP

omit [DecidableEq σ] in
lemma tuplePrimeFamily_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p)).ideal=p :=
  tupleRepresentative_at_product tuples hne hinj p hp

lemma tuple_product_injective (L : σ→Finset (Ideal Eis))
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P∈L i, Prime P) (tuples : Finset (σ→Ideal Eis))
    (hT : ∀ p∈tuples, ∀ i, p i∈L i) :
    Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hp).mono hT

end
end SevenEighths.InverseReflectedPhase

end OAI
