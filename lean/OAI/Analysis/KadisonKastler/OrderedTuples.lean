import OAI.Analysis.KadisonKastler.IncidenceMatrices
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange

namespace OAI

/-!
# Ordering fibres of distinct label tuples

An injective ordered tuple determines its underlying subset. Every fibre
consists of the bijections from the positions onto that subset, so its
cardinality is exactly the factorial of the number of positions.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def OrderedLabelTuple (W : Finset α) (p : ℕ) :=
  {f : Fin p → α // Function.Injective f ∧ ∀ i, f i ∈ W}

instance (W : Finset α) (p : ℕ) : Fintype (OrderedLabelTuple W p) := by
  classical
  unfold OrderedLabelTuple
  infer_instance

/-- Forget the ordering of the distinct labels. -/
def tupleSubset {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) : WordSubset W p :=
  ⟨univ.image t.val,
    by
      intro a ha
      obtain ⟨i, _, rfl⟩ := mem_image.mp ha
      exact t.property.2 i,
    by
      rw [card_image_of_injective _ t.property.1]
      simp⟩

omit [Fintype α] in
@[simp]
theorem mem_tupleSubset {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) (a : α) :
    a ∈ (tupleSubset t).val ↔ ∃ i, t.val i = a := by
  simp [tupleSubset]

/-- Realize a bijective enumeration of a subset as an ordered tuple in `W`. -/
def orderedTupleOfEquiv {W : Finset α} {p : ℕ} (B : WordSubset W p)
    (e : Fin p ≃ B.val) : OrderedLabelTuple W p :=
  ⟨fun i => (e i).val,
    by
      intro i j hij
      exact e.injective (Subtype.ext hij),
    fun i => B.property.1 (e i).property⟩

omit [Fintype α] in
@[simp]
theorem tupleSubset_orderedTupleOfEquiv {W : Finset α} {p : ℕ} (B : WordSubset W p)
    (e : Fin p ≃ B.val) : tupleSubset (orderedTupleOfEquiv B e) = B := by
  apply Subtype.ext
  ext a
  rw [mem_tupleSubset]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro ha
    obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- Enumerate the subset from an ordered tuple known to lie over it. -/
def orderedTupleEquiv {W : Finset α} {p : ℕ} (B : WordSubset W p)
    (t : OrderedLabelTuple W p) (ht : tupleSubset t = B) : Fin p ≃ B.val :=
  Equiv.ofBijective
    (fun i => ⟨t.val i, by
      rw [← ht, mem_tupleSubset]
      exact ⟨i, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact t.property.1 (congrArg Subtype.val hij),
     by
      intro a
      have ha : a.val ∈ (tupleSubset t).val := by rw [ht]; exact a.property
      obtain ⟨i, hi⟩ := (mem_tupleSubset t a.val).mp ha
      exact ⟨i, Subtype.ext hi⟩⟩

/-- An ordering fibre is the type of bijections from its positions onto
its underlying subset. -/
def orderedTupleFiberEquiv {W : Finset α} {p : ℕ} (B : WordSubset W p) :
    {t : OrderedLabelTuple W p // tupleSubset t = B} ≃ (Fin p ≃ B.val) where
  toFun t := orderedTupleEquiv B t.val t.property
  invFun e := ⟨orderedTupleOfEquiv B e, tupleSubset_orderedTupleOfEquiv B e⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

/-- Every `p`-element subset has exactly `p!` orderings. -/
theorem card_orderedTupleFiber {W : Finset α} {p : ℕ} (B : WordSubset W p) :
    Fintype.card {t : OrderedLabelTuple W p // tupleSubset t = B} = p.factorial := by
  classical
  have hcard : Fintype.card (Fin p) = Fintype.card B.val := by
    rw [Fintype.card_fin, Fintype.card_coe, B.property.2]
  rw [Fintype.card_congr (orderedTupleFiberEquiv B),
    Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

/-- The finset form used by the matrix replication estimate. -/
theorem card_filter_tupleSubset {W : Finset α} {p : ℕ} (B : WordSubset W p) :
    #{t : OrderedLabelTuple W p | tupleSubset t = B} = p.factorial := by
  classical
  rw [← Fintype.card_subtype]
  exact card_orderedTupleFiber B

/-- Count ordered selections by first choosing their underlying subset. -/
theorem card_orderedLabelTuple (W : Finset α) (p : ℕ) :
    Fintype.card (OrderedLabelTuple W p) = W.card.choose p * p.factorial := by
  classical
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (tupleSubset (W := W) (p := p))),
    Fintype.card_sigma]
  simp only [card_orderedTupleFiber, sum_const, card_univ, smul_eq_mul, card_wordSubset]

/-- In particular, all orderings of an `r`-element label set number `r!`. -/
theorem card_full_orderedLabelTuple (W : Finset α) {r : ℕ} (hr : W.card = r) :
    Fintype.card (OrderedLabelTuple W r) = r.factorial := by
  rw [card_orderedLabelTuple, hr, Nat.choose_self, one_mul]

/-- The ordered list used to form a noncommutative word. -/
def orderedTupleList {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) : List α :=
  List.ofFn t.val

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem length_orderedTupleList {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) :
    (orderedTupleList t).length = p := by
  exact List.length_ofFn

omit [Fintype α] [DecidableEq α] in
theorem nodup_orderedTupleList {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) :
    (orderedTupleList t).Nodup :=
  List.nodup_ofFn_ofInjective t.property.1

omit [Fintype α] in
@[simp]
theorem toFinset_orderedTupleList {W : Finset α} {p : ℕ} (t : OrderedLabelTuple W p) :
    (orderedTupleList t).toFinset = (tupleSubset t).val := by
  ext a
  simp only [List.mem_toFinset, orderedTupleList, List.mem_ofFn, mem_tupleSubset]

omit [Fintype α] [DecidableEq α] in
theorem orderedTupleList_injective {W : Finset α} {p : ℕ} :
    Function.Injective (orderedTupleList (W := W) (p := p)) := by
  intro t u h
  apply Subtype.ext
  exact List.ofFn_injective h

end

end KadisonKastler

end OAI
