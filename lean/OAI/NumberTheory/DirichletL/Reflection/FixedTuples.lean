import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
import OAI.NumberTheory.DirichletL.Reflection.ActiveProducts

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) : Finset (σ→Ideal Eis) :=
  (Fintype.piFinset L).filter fun p => ∀ j i,p i≠F j

lemma mem_fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (p : σ→Ideal Eis) :
    p∈fixedSlotTupleSet L F ↔ (∀ i,p i∈L i) ∧ ∀ j i,p i≠F j := by
  simp only [fixedSlotTupleSet,Finset.mem_filter,Fintype.mem_piFinset]

lemma fixedSlotTupleSet_product_injective (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P) :
    Set.InjOn slotTupleProduct (↑(fixedSlotTupleSet L F) : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hprime).mono (fun p hp => (mem_fixedSlotTupleSet L F p).mp hp |>.1)

def supportedSlotTupleEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃ {p : fixedSlotTupleSet L F // IsCoprime K (slotTupleProduct p.val)} where
  toFun p := ⟨⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩⟩,p.property.1⟩
  invFun p := ⟨fun i => ⟨p.val.val i,((mem_fixedSlotTupleSet L F _).mp p.val.property).1 i⟩,
    ⟨p.property,((mem_fixedSlotTupleSet L F _).mp p.val.property).2⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := rfl

def supportedSlotProductEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val} := by
  let f := fun p : supportedSlotChoices L F K =>
    (⟨⟨slotTupleProduct (fun i => (p.val i).val),Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩,p.property.1⟩ :
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val})
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have hv := congrArg (fun P => P.val.val) he
    have hh := fixedSlotTupleSet_product_injective L F hL hprime
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (q.val i).property,q.property.2⟩) hv
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hh i)
  · intro P
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp P.val.property
    let q : supportedSlotChoices L F K := ⟨fun i => ⟨p i,((mem_fixedSlotTupleSet L F p).mp hp).1 i⟩,
      ⟨by change IsCoprime K (slotTupleProduct p);rw [he];exact P.property,((mem_fixedSlotTupleSet L F p).mp hp).2⟩⟩
    refine ⟨q,?_⟩
    apply Subtype.ext
    exact Subtype.ext he

lemma supportedSlotProductEquiv_apply (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) (p : supportedSlotChoices L F K) :
    ((supportedSlotProductEquiv L F hL hprime K) p).val.val=∏ i,(p.val i).val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
