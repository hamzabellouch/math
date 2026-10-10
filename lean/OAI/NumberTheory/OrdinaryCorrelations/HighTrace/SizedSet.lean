import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.FactorialAssignments

variable {P : Type*} [Fintype P]

abbrev SizedSet (P : Type*) (n : ℕ) := {s : Finset P // s.card = n}

abbrev NamedBlock (P : Type*) (n : ℕ) := Fin n ↪ P

def forgetBlock {n : ℕ} (f : NamedBlock P n) : SizedSet P n :=
  ⟨univ.image f, by rw [card_image_of_injective _ f.injective]; simp⟩

abbrev BlockNames {n : ℕ} (s : SizedSet P n) := Fin n ≃ s.val

def canonicalNames {n : ℕ} (s : SizedSet P n) : BlockNames s :=
  (s.val.equivFinOfCardEq s.property).symm

omit [Fintype P] in
lemma card_blockNames {n : ℕ} (s : SizedSet P n) :
    Fintype.card (BlockNames s) = n.factorial := by
  simpa only [Fintype.card_fin] using Fintype.card_equiv (canonicalNames s)

def namesOfBlock {n : ℕ} (f : NamedBlock P n) : BlockNames (forgetBlock f) where
  toFun i := ⟨f i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  invFun p := Classical.choose (mem_image.mp p.property)
  left_inv i := by
    apply f.injective
    exact (Classical.choose_spec (mem_image.mp (show f i ∈ univ.image f from
      mem_image.mpr ⟨i,mem_univ _,rfl⟩))).2
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec (mem_image.mp p.property)).2

def blockOfNames {n : ℕ} (s : SizedSet P n) (e : BlockNames s) : NamedBlock P n :=
  ⟨fun i => (e i).val, fun _ _ equality => e.injective (Subtype.ext equality)⟩

omit [Fintype P] in
lemma forgetBlock_ofNames {n : ℕ} (s : SizedSet P n) (e : BlockNames s) :
    forgetBlock (blockOfNames s e) = s := by
  apply Subtype.ext
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact (e i).property
  · intro hp
    obtain ⟨i,hi⟩ := e.surjective ⟨p,hp⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

omit [Fintype P] in
lemma namedSigma_ext {n : ℕ} {x y : (s : SizedSet P n) × BlockNames s}
    (h : ∀ i, (x.2 i).val = (y.2 i).val) : x = y := by
  rcases x with ⟨s,e⟩
  rcases y with ⟨t,f⟩
  have hst : s = t := by
    apply Subtype.ext
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := e.surjective ⟨p,hp⟩
      have he : (e i).val = p := congrArg Subtype.val hi
      simpa only [← h i,he] using (f i).property
    · intro hp
      obtain ⟨i,hi⟩ := f.surjective ⟨p,hp⟩
      have hf : (f i).val = p := congrArg Subtype.val hi
      simpa only [h i,hf] using (e i).property
  subst t
  have hef : e = f := Equiv.ext (fun i => Subtype.ext (h i))
  subst f
  rfl

def blockEquiv (P : Type*) [Fintype P] (n : ℕ) :
    NamedBlock P n ≃ (s : SizedSet P n) × BlockNames s where
  toFun f := ⟨forgetBlock f,namesOfBlock f⟩
  invFun x := blockOfNames x.1 x.2
  left_inv f := by ext i; rfl
  right_inv x := by
    apply namedSigma_ext
    intro i
    rfl

variable {T : Type*} [Fintype T] (j : T → ℕ)

abbrev Unordered := ∀ t, SizedSet P (j t)
abbrev Named := ∀ t, NamedBlock P (j t)

def forget (x : Named (P := P) j) : Unordered (P := P) j := fun t => forgetBlock (x t)

abbrev Names (q : Unordered (P := P) j) := ∀ t, BlockNames (q t)

omit [Fintype P] in
lemma card_names (q : Unordered (P := P) j) :
    Fintype.card (Names j q) = ∏ t, (j t).factorial := by
  change Fintype.card (∀ t, BlockNames (q t)) = _
  rw [Fintype.card_pi]
  simp only [card_blockNames]

def piSigmaEquiv {ι : Type*} {α : ι → Type*} {β : (i : ι) → α i → Type*} :
    (∀ i, (a : α i) × β i a) ≃ ((a : ∀ i, α i) × ∀ i, β i (a i)) where
  toFun x := ⟨fun i => (x i).1,fun i => (x i).2⟩
  invFun x i := ⟨x.1 i,x.2 i⟩
  left_inv x := by funext i; rfl
  right_inv x := by cases x; rfl

def namedEquiv : Named (P := P) j ≃ (q : Unordered (P := P) j) × Names j q :=
  (Equiv.piCongrRight (fun t => blockEquiv P (j t))).trans piSigmaEquiv

omit [Fintype T] in
@[simp] lemma namedEquiv_fst (x : Named (P := P) j) : (namedEquiv j x).1 = forget j x := rfl

theorem sum_names (V : Unordered (P := P) j → Prop) (W : Unordered (P := P) j → ℝ) :
    (∑ q : Unordered (P := P) j, ∑ _name : Names j q, if V q then W q else 0) =
      (∏ t, (j t).factorial : ℕ) * ∑ q : Unordered (P := P) j, if V q then W q else 0 := by
  simp only [sum_const, card_univ, nsmul_eq_mul, card_names, ← mul_sum]

theorem sum_named_slots (V : Unordered (P := P) j → Prop)
    (W : Unordered (P := P) j → ℝ) :
    (∑ x : Named (P := P) j, if V (forget j x) then W (forget j x) else 0) =
      (∏ t, (j t).factorial : ℕ) * ∑ q : Unordered (P := P) j, if V q then W q else 0 := by
  rw [← sum_names j V W]
  calc
    _ = ∑ x : (q : Unordered (P := P) j) × Names j q, if V x.1 then W x.1 else 0 :=
      Fintype.sum_equiv (namedEquiv j) _ _ (by intro x; rfl)
    _ = _ := Fintype.sum_sigma _

theorem factorial_quotient (V : Unordered (P := P) j → Prop)
    (W : Unordered (P := P) j → ℝ) :
    (∑ q : Unordered (P := P) j, if V q then W q else 0) =
      (∑ x : Named (P := P) j, if V (forget j x) then W (forget j x) else 0) /
        (∏ t, (j t).factorial : ℕ) := by
  have hpos : (0 : ℝ) < (∏ t, (j t).factorial : ℕ) := by positivity
  rw [sum_named_slots, mul_div_cancel_left₀ _ hpos.ne']

def edgeLabels {E : Type*} [DecidableEq E] (shape : T → Finset E) (value : P → ℕ)
    (q : Unordered (P := P) j) (e : E) : ℕ :=
  ∏ t, if e ∈ shape t then ∏ p ∈ (q t).val, value p else 1

def namedEdgeLabels {E : Type*} [DecidableEq E] (shape : T → Finset E) (value : P → ℕ)
    (x : Named (P := P) j) (e : E) : ℕ :=
  ∏ t, if e ∈ shape t then ∏ i, value (x t i) else 1

omit [Fintype P] in
lemma named_edgeLabels_eq {E : Type*} [DecidableEq E] (shape : T → Finset E)
    (value : P → ℕ) (x : Named (P := P) j) :
    namedEdgeLabels j shape value x = edgeLabels j shape value (forget j x) := by
  funext e
  apply prod_congr rfl
  intro t _
  split_ifs
  · exact (prod_image (fun i _ k _ hik => (x t).injective hik)).symm
  · rfl

omit [Fintype P] in
lemma label_predicate_invariant {E : Type*} [DecidableEq E]
    (shape : T → Finset E) (value : P → ℕ) (test : (E → ℕ) → Prop)
    (x : Named (P := P) j) :
    test (namedEdgeLabels j shape value x) ↔ test (edgeLabels j shape value (forget j x)) := by
  rw [named_edgeLabels_eq]

abbrev Slots := ∀ t, Fin (j t) → P

def realize (x : Named (P := P) j) : Slots (P := P) j := fun t i => x t i

omit [Fintype P] [Fintype T] in
lemma realize_injective : Function.Injective (realize (P := P) j) := by
  intro x y h
  funext t
  apply Function.Embedding.ext
  intro i
  exact congrFun (congrFun h t) i

def unorderedWeight (w : T → P → ℝ) (q : Unordered (P := P) j) : ℝ :=
  ∏ t, ∏ p ∈ (q t).val, w t p

def slotWeight (w : T → P → ℝ) (x : Slots (P := P) j) : ℝ :=
  ∏ t, ∏ i, w t (x t i)

omit [Fintype P] in
lemma slotWeight_nonneg (w : T → P → ℝ) (hw : ∀ t p, 0 ≤ w t p) (x : Slots (P := P) j) :
    0 ≤ slotWeight j w x :=
  prod_nonneg (fun t _ => prod_nonneg (fun i _ => hw t (x t i)))

omit [Fintype P] in
lemma unorderedWeight_forget (w : T → P → ℝ) (x : Named (P := P) j) :
    unorderedWeight j w (forget j x) = slotWeight j w (realize j x) := by
  apply prod_congr rfl
  intro t _
  exact prod_image (fun i _ k _ hik => (x t).injective hik)

lemma sum_slotWeight (w : T → P → ℝ) :
    (∑ x : Slots (P := P) j, slotWeight j w x) = ∏ t, (∑ p, w t p)^(j t) := by
  unfold slotWeight
  rw [← Fintype.prod_sum (fun (t : T) (y : Fin (j t) → P) => ∏ i, w t (y i))]
  apply prod_congr rfl
  intro t _
  rw [← Fintype.prod_sum (fun (_i : Fin (j t)) (p : P) => w t p)]
  simp

theorem unordered_sum_bound (V : Unordered (P := P) j → Prop)
    (w : T → P → ℝ) (hw : ∀ t p, 0 ≤ w t p) :
    (∑ q : Unordered (P := P) j, if V q then unorderedWeight j w q else 0) ≤
      ∏ t, (∑ p, w t p)^(j t) / (j t).factorial := by
  have hn : (∑ x : Named (P := P) j,
      if V (forget j x) then unorderedWeight j w (forget j x) else 0) ≤
      ∑ x : Slots (P := P) j, slotWeight j w x := by
    calc
      _ ≤ ∑ x : Named (P := P) j, slotWeight j w (realize j x) := by
        apply sum_le_sum
        intro x _
        rw [unorderedWeight_forget]
        split_ifs
        · exact le_refl _
        · exact slotWeight_nonneg j w hw _
      _ = ∑ x ∈ univ.image (realize (P := P) j), slotWeight j w x :=
        (sum_image (fun x _ y _ h => realize_injective j h)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun x _ _ => slotWeight_nonneg j w hw x)
  rw [factorial_quotient, prod_div_distrib, ← Nat.cast_prod]
  exact div_le_div_of_nonneg_right (hn.trans_eq (sum_slotWeight j w)) (by positivity)

theorem multiplicity_sum_bound [DecidableEq T] (x : T → ℝ) (hx : ∀ t, 0 ≤ x t) (N : T → ℕ) :
    (∑ j : ∀ t, Fin (N t), ∏ t, x t ^ (j t).val / (j t).val.factorial) ≤
      Real.exp (∑ t, x t) := by
  rw [← Fintype.prod_sum (fun (t : T) (n : Fin (N t)) => x t ^ n.val / n.val.factorial), Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro t _
    apply sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (hx t) _) (Nat.cast_nonneg _)
  · intro t _
    rw [← Finset.sum_range (fun n => x t ^ n / (n.factorial : ℝ))]
    exact Real.sum_le_exp_of_nonneg (hx t) (N t)

end OrdinaryCorrelations.FactorialAssignments

end

end OAI
