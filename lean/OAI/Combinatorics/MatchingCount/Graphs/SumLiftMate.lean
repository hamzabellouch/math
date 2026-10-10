import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.ThresholdGraph

namespace OAI

namespace MatchingFPRAS.Switching

section

open Finset

variable {V W : Type*}

def sumLiftMate (m : Mate V) : Mate (V ⊕ W) :=
  ⟨Sum.map m.val id,by intro x; cases x <;> simp⟩

@[simp] lemma sumLiftMate_inl (m : Mate V) (a : V) :
    (sumLiftMate (W := W) m).val (Sum.inl a)=Sum.inl (m.val a) := rfl

@[simp] lemma sumLiftMate_inr (m : Mate V) (a : W) :
    (sumLiftMate m).val (Sum.inr a)=(Sum.inr a : V ⊕ W) := rfl

def sumRetractMate (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) : Mate V := by
  let f : V → V := fun a => Sum.elim id (fun _ => a) (q.val (Sum.inl a))
  have hf : ∀ a, Sum.inl (f a)=q.val (Sum.inl a) := by
    intro a
    cases he : q.val (Sum.inl a) with
    | inl b => simp [f,he]
    | inr w =>
      have hh := q.property (Sum.inl a)
      rw [he,hfix] at hh
      contradiction
  refine ⟨f,?_⟩
  intro a
  apply Sum.inl_injective (β := W)
  rw [hf,hf,q.property]

lemma sumRetractMate_inl (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) (a : V) :
    Sum.inl ((sumRetractMate q hfix).val a)=q.val (Sum.inl a) := by
  cases he : q.val (Sum.inl a) with
  | inl b => simp [sumRetractMate,he]
  | inr w =>
    have hh := q.property (Sum.inl a)
    rw [he,hfix] at hh
    contradiction

lemma sumLift_retract (q : Mate (V ⊕ W)) (hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w) :
    sumLiftMate (sumRetractMate q hfix)=q := by
  apply Subtype.ext; funext a
  cases a with
  | inl a => exact sumRetractMate_inl q hfix a
  | inr w => exact (hfix w).symm

lemma sumLift_holes [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq (V ⊕ W)]
    (m : Mate V) (R : Finset V) :
    HasHoles (sumLiftMate (W := W) m) (R.map ⟨Sum.inl,Sum.inl_injective⟩)ᶜ ↔ HasHoles m Rᶜ := by
  constructor
  · intro h a
    simpa using h (Sum.inl a)
  · intro h a
    cases a with
    | inl a => simpa using h a
    | inr w => simp

lemma internal_fixed_of_terminal_holes [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq (V ⊕ W)]
    (q : Mate (V ⊕ W)) (R : Finset V)
    (hq : HasHoles q (R.map ⟨Sum.inl,Sum.inl_injective⟩)ᶜ) (w : W) :
    q.val (Sum.inr w)=Sum.inr w := (hq (Sum.inr w)).mpr (by simp)

lemma sumLift_weight [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder (V ⊕ W)]
    (hord : ∀ a b : V, ((Sum.inl a : V ⊕ W) < Sum.inl b) ↔ a < b)
    (B : V → V → ℝ) (B' : (V ⊕ W) → (V ⊕ W) → ℝ)
    (hB : ∀ a b, B' (Sum.inl a) (Sum.inl b)=B a b) (m : Mate V) :
    weight B' (sumLiftMate m)=weight B m := by
  simp [weight,Fintype.prod_sum_type,hord,hB]

theorem pairingCapacity_sum_inl [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder (V ⊕ W)]
    (hord : ∀ a b : V, ((Sum.inl a : V ⊕ W) < Sum.inl b) ↔ a < b)
    (B : V → V → ℝ) (B' : (V ⊕ W) → (V ⊕ W) → ℝ)
    (hB : ∀ a b, B' (Sum.inl a) (Sum.inl b)=B a b)
    (R : Finset V) (hR : Even R.card)
    (hR' : Even (R.map ⟨Sum.inl,Sum.inl_injective (β := W)⟩).card) :
    pairingCapacity B' (R.map ⟨Sum.inl,Sum.inl_injective⟩) hR'=pairingCapacity B R hR := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro q hq
    have hholes := (mem_matchings q _).mp hq
    have hfix : ∀ w, q.val (Sum.inr w)=Sum.inr w := by
      intro w
      exact (hholes (Sum.inr w)).mpr (by simp)
    let m := sumRetractMate q hfix
    have hqm : sumLiftMate m=q := sumLift_retract q hfix
    have hm : HasHoles m Rᶜ := by
      intro a
      have hh := hholes (Sum.inl a)
      rw [← hqm] at hh
      simpa using hh
    rw [← hqm,sumLift_weight hord B B' hB]
    exact weight_le_pairingCapacity B R hR m hm
  · apply Finset.sup'_le
    intro m hm
    have hholes := (mem_matchings m _).mp hm
    rw [← sumLift_weight hord B B' hB]
    apply weight_le_pairingCapacity B' _ hR' (sumLiftMate m)
    intro a
    cases a with
    | inl a => simpa using hholes a
    | inr a => simp

theorem ChargeTrace.capacity_bound_decidable [Fintype V] [LinearOrder V]
    (dec : DecidableEq V) {B : V → V → ℝ}
    (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    {U W : Finset V} {F : ℝ} (h : @ChargeTrace V dec B U W F) (hU : Even U.card) :
    ∃ hW : Even W.card, pairingCapacity B U hU * F ≤ pairingCapacity B W hW := by
  have he : dec = (inferInstance : LinearOrder V).toDecidableEq := Subsingleton.elim _ _
  subst dec
  exact h.capacity_bound hB hB0 htri hU

end

variable {V : Type*}

lemma ChargeTrace.factor_nonneg [DecidableEq V] {B : V → V → ℝ}
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) : 0 ≤ F := by
  cases h with
  | done => norm_num
  | remove _ _ _ _ _ _ _ _ _ _ _ _ _ hf hF => exact mul_nonneg hf hF
  | replace _ _ _ _ _ _ _ _ _ _ hf hF => exact mul_nonneg hf hF

end MatchingFPRAS.Switching

namespace MatchingFPRAS.Subdivision

open Finset

abbrev Selection (m : ℕ) := Fin (m+1) → Bool

def Valid {m : ℕ} (holes : Finset (Fin m)) (b : Selection m) : Prop :=
  ∀ i : Fin m, if i ∈ holes then b i.castSucc = false ∧ b i.succ = false
    else b i.castSucc ≠ b i.succ

def alternating (a : Bool) (i : ℕ) : Bool := if i % 2 = 0 then a else !a

@[simp] theorem alternating_zero (a : Bool) : alternating a 0 = a := by
  simp [alternating]

@[simp] theorem alternating_succ (a : Bool) (i : ℕ) :
    alternating a (i+1) = !(alternating a i) := by
  by_cases h : i % 2 = 0
  · have hs : (i+1)%2 = 1 := by omega
    simp [alternating,h,hs]
  · have hs : i%2=1 := by omega
    have ht : (i+1)%2=0 := by omega
    simp [alternating,hs,ht]

@[simp] theorem alternating_add_two (a : Bool) (i : ℕ) :
    alternating a (i+2) = alternating a i := by
  rw [show i+2=(i+1)+1 by omega, alternating_succ, alternating_succ]
  simp

lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ b = !a := by
  cases a <;> cases b <;> simp

theorem intact_iff {m : ℕ} (b : Selection m) :
    Valid ∅ b ↔ ∀ i : Fin (m+1), b i = alternating (b 0) i.val := by
  constructor
  · intro h i
    have hstep (j : Fin m) : b j.succ = !(b j.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa [Valid] using h j
    have aux (k : ℕ) (hk : k < m+1) : b ⟨k,hk⟩ = alternating (b 0) k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [alternating_succ]
        have hk' : k < m := by omega
        have he := hstep ⟨k,hk'⟩
        simpa only [Fin.succ_mk, Fin.castSucc_mk, ih (by omega)] using he
    exact aux i.val i.isLt
  · intro h i
    simp only [Finset.notMem_empty, ↓reduceIte]
    rw [h i.castSucc, h i.succ]
    simp only [Fin.val_castSucc, Fin.val_succ, alternating_succ]
    cases alternating (b 0) i.val <;> decide

theorem intact_terminals {m : ℕ} (hm : Even m) (b : Selection m)
    (h : Valid ∅ b) : b (Fin.last m) = b 0 := by
  rw [(intact_iff b).mp h]
  simp [alternating, Nat.even_iff.mp hm]

theorem alternating_valid (m : ℕ) (a : Bool) :
    Valid ∅ (fun i : Fin (m+1) => alternating a i.val) := by
  apply (intact_iff _).mpr
  intro i
  simp

@[simp] theorem alternating_not (a : Bool) (i : ℕ) :
    alternating (!a) i = !(alternating a i) := by
  unfold alternating
  split_ifs <;> simp

def wordWeight (a : Bool) : List ℝ → ℝ
  | [] => 1
  | x::xs => (if a then x else 1) * wordWeight (!a) xs

@[simp] theorem wordWeight_nil (a : Bool) : wordWeight a [] = 1 := rfl

@[simp] theorem wordWeight_pair (a : Bool) (x : ℝ) (xs : List ℝ) :
    wordWeight a (x::x::xs) = x * wordWeight a xs := by
  cases a <;> simp [wordWeight]

def duplicate (xs : List ℝ) : List ℝ := xs.flatMap (fun x => [x,x])

@[simp] theorem duplicate_nil : duplicate [] = [] := rfl

@[simp] theorem duplicate_cons (x : ℝ) (xs : List ℝ) :
    duplicate (x::xs) = x::x::duplicate xs := by simp [duplicate]

@[simp] theorem duplicate_length (xs : List ℝ) :
    (duplicate xs).length = 2*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

 theorem paired_prefix_weight (a : Bool) (xs ys : List ℝ) :
    wordWeight a (duplicate xs ++ ys) = xs.prod * wordWeight a ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

theorem profile_weight (a : Bool) (left right : List ℝ) (lam : ℝ) :
    wordWeight a (duplicate left ++ [lam] ++ duplicate right) =
      left.prod * right.prod * (if a then lam else 1) := by
  rw [List.append_assoc, paired_prefix_weight]
  simp only [List.singleton_append, wordWeight]
  have h := paired_prefix_weight (!a) right []
  simp only [List.append_nil, wordWeight_nil, mul_one] at h
  rw [h]
  ring

theorem wordWeight_ofFn (n : ℕ) (w : Fin n → ℝ) (a : Bool) :
    wordWeight a (List.ofFn w) = ∏ i, (if alternating a i.val then w i else 1) := by
  induction n generalizing a with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [wordWeight, Fin.val_zero, alternating_zero]
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp

noncomputable def selectedWeight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m) : ℝ :=
  ∏ i, if b i then w i else 1

 theorem intact_weight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m)
    (h : Valid ∅ b) : selectedWeight w b = wordWeight (b 0) (List.ofFn w) := by
  rw [wordWeight_ofFn]
  unfold selectedWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [(intact_iff b).mp h]

variable {V E : Type*} [Fintype V] [Fintype E]

def LogicalPerfect (u v : E → V) (s : E → Bool) : Prop :=
  ∀ x, ∃! e, s e = true ∧ (u e = x ∨ v e = x)

def FamilyPerfect (u v : E → V) (m : ℕ) (b : E → Selection m) : Prop :=
  (∀ e, Valid ∅ (b e)) ∧
    ∀ x, ∃! e, (b e 0 = true ∧ u e = x) ∨
      (b e (Fin.last m) = true ∧ v e = x)

omit [Fintype V] [Fintype E] in
 theorem family_iff [Fintype V] [Fintype E]
    {u v : E → V} {m : ℕ} (hm : Even m) (b : E → Selection m) :
    FamilyPerfect u v m b ↔
      (∀ e, Valid ∅ (b e)) ∧ LogicalPerfect u v (fun e => b e 0) := by
  unfold FamilyPerfect LogicalPerfect
  constructor
  · rintro ⟨hp,ht⟩
    refine ⟨hp,?_⟩
    have he (e) := intact_terminals hm (b e) (hp e)
    simpa only [he, ← and_or_left] using ht
  · rintro ⟨hp,ht⟩
    refine ⟨hp,?_⟩
    have he (e) := intact_terminals hm (b e) (hp e)
    simpa only [he, ← and_or_left] using ht

def familyEquiv (u v : E → V) (m : ℕ) (hm : Even m) :
    {b : E → Selection m // FamilyPerfect u v m b} ≃
      {s : E → Bool // LogicalPerfect u v s} where
  toFun b := ⟨fun e => b.val e 0, ((family_iff hm b.val).mp b.property).2⟩
  invFun s := ⟨fun e i => alternating (s.val e) i.val,
    (family_iff hm _).mpr ⟨fun e => alternating_valid m (s.val e), by
      simpa only [Fin.val_zero, alternating_zero] using s.property⟩⟩
  left_inv b := by
    apply Subtype.ext
    funext e i
    exact ((intact_iff (b.val e)).mp (b.property.1 e) i).symm
  right_inv s := by
    apply Subtype.ext
    funext e
    simp

noncomputable def logicalPartition (u v : E → V) (lam : E → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {s : E → Bool // LogicalPerfect u v s}
  exact ∑ s : {s : E → Bool // LogicalPerfect u v s},
    ∏ e, if s.val e then lam e else 1

noncomputable def realPartition (u v : E → V) (m : ℕ)
    (w : E → Fin (m+1) → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {b : E → Selection m // FamilyPerfect u v m b}
  exact ∑ b : {b : E → Selection m // FamilyPerfect u v m b},
    ∏ e, selectedWeight (w e) (b.val e)

omit [Fintype V] [Fintype E] in
theorem family_weight [Fintype V] [Fintype E] (u v : E → V) (m : ℕ) (_hm : Even m)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e))
    (b : E → Selection m) (hb : FamilyPerfect u v m b) :
    (∏ e, selectedWeight (w e) (b e)) =
      (∏ e, (left e).prod * (right e).prod) *
        ∏ e, if b e 0 then lam e else 1 := by
  classical
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [intact_weight _ _ (hb.1 e), hw e, profile_weight]

theorem real_partition_identity (u v : E → V) (m : ℕ) (hm : Even m)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    realPartition u v m w =
      (∏ e, (left e).prod * (right e).prod) * logicalPartition u v lam := by
  classical
  let := Fintype.ofFinite {s : E → Bool // LogicalPerfect u v s}
  let := Fintype.ofFinite {b : E → Selection m // FamilyPerfect u v m b}
  unfold realPartition logicalPartition
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (familyEquiv u v m hm)
  intro b
  exact family_weight u v m hm w left right lam hw b.val b.property

end MatchingFPRAS.Subdivision

end OAI
