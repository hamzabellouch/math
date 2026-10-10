import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryOccurrenceVariables
open Construction

@[reducible] def InternalKey : {l : ℕ} → History l → Type
  | _, .leaf _ => Empty
  | _, .node _ _ u _ _ left right =>
      Fin u.length ⊕ (InternalKey left ⊕ InternalKey right)

instance internalKeyFintype : {l : ℕ} → (h : History l) → Fintype (InternalKey h)
  | _, .leaf _ => inferInstanceAs (Fintype Empty)
  | _, .node _ _ u _ _ left right => by
      letI := internalKeyFintype left
      letI := internalKeyFintype right
      exact inferInstanceAs (Fintype (Fin u.length ⊕ (InternalKey left ⊕ InternalKey right)))

def internalSlot : {l : ℕ} → (h : History l) → InternalKey h → SmallSlot
  | _, .leaf _ => fun i => Empty.elim i
  | _, .node _ _ u _ _ left right =>
      Sum.elim u.get (Sum.elim (internalSlot left) (internalSlot right))

@[reducible] def Key {l : ℕ} (h : History l) :=
  Bool ⊕ (Fin h.root.small.length ⊕ InternalKey h)

instance keyFintype {l : ℕ} (h : History l) : Fintype (Key h) :=
  inferInstanceAs (Fintype (Bool ⊕ (Fin h.root.small.length ⊕ InternalKey h)))

def integerSample {l : ℕ} (h : History l) : Key h → ℤ
  | .inl false => h.root.giantPlus
  | .inl true => h.root.giantMinus
  | .inr (.inl i) => (h.root.small.get i).value
  | .inr (.inr i) => (internalSlot h i).value

def rationalSample {l : ℕ} (h : History l) (i : Key h) : ℚ := integerSample h i

theorem internalKey_card {l : ℕ} (h : History l) :
    Fintype.card (InternalKey h) = h.internalOccurrences.length := by
  induction h with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
      simp only [InternalKey,Fintype.card_sum,Fintype.card_fin,History.internalOccurrences,
        List.length_append,ihl,ihr]
      omega

theorem key_card {l : ℕ} (h : History l) :
    Fintype.card (Key h) = 2 + h.root.small.length + h.internalOccurrences.length := by
  simp only [Key,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,internalKey_card]
  omega

theorem prod_internalSlot {M : Type*} [CommMonoid M] (f : SmallSlot → M)
    {l : ℕ} (h : History l) :
    (∏ i : InternalKey h, f (internalSlot h i)) =
      (h.internalOccurrences.map f).prod := by
  induction h with
  | leaf a => simp [InternalKey,internalSlot,History.internalOccurrences]
  | @node l a p u hp hm left right ihl ihr =>
    simp only [InternalKey,Fintype.prod_sum_type,internalSlot,Sum.elim_inl,Sum.elim_inr,ihl,ihr,
      History.internalOccurrences,List.map_append,List.prod_append]
    have hprod : (∏ i : Fin u.length, f (u.get i)) = (u.map f).prod := by
      rw [← List.prod_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map u f
    rw [hprod]
    exact (mul_assoc _ _ _).symm

end Ostmann.Arithmetic.HistoryOccurrenceVariables

end

end OAI
