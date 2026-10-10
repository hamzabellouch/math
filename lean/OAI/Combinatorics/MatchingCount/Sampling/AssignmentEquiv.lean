import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Edge2

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {V W L : Type*} [Fintype V] [Fintype W] [Fintype L]
  [DecidableEq V] [DecidableEq W] [DecidableEq L]

noncomputable def assignmentEquiv (b : V → Finset L) (c : W → Finset L)
    (e : V ≃ W) (he : ∀ x,c (e x)=b x) : Assignment b ≃ Assignment c where
  toFun f := ⟨fun y => f.val (e.symm y),fun y => by
    have hy : c y=b (e.symm y) := by simpa using he (e.symm y)
    rw [hy]; exact f.property (e.symm y)⟩
  invFun f := ⟨fun x => f.val (e x),fun x => by rw [←he]; exact f.property _⟩
  left_inv f := Subtype.ext (by funext x; simp)
  right_inv f := Subtype.ext (by funext x; simp)

omit [Fintype L] [DecidableEq V] [DecidableEq W] in
lemma fiberCount_equiv [Fintype L] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (f : V → L) (g : W → L)
    (h : ∀ x,g (e x)=f x) (l : L) : fiberCount f l=fiberCount g l := by
  unfold fiberCount
  exact Fintype.card_congr (e.subtypeEquiv (fun x => by rw [h]))

lemma assignmentPartition_equiv (b : V → Finset L) (c : W → Finset L)
    (e : V ≃ W) (he : ∀ x,c (e x)=b x) (w : L → ℕ → ℕ) :
    assignmentPartition b w = assignmentPartition c w := by
  classical
  unfold assignmentPartition
  apply Fintype.sum_equiv (assignmentEquiv b c e he)
  intro f
  apply prod_congr rfl
  intro l hl
  congr 1
  apply fiberCount_equiv e
  intro x
  simp [assignmentEquiv]

abbrev Private (b : V → Finset L) (l : L) := {x : V // b x={l}}

abbrev Shared (b : V → Finset L) (l : L) := {x : V // l∈b x ∧ b x≠{l}}

abbrev Outside (b : V → Finset L) (l : L) := {x : V // l∉b x}

noncomputable def splitLeaf (b : V → Finset L) (l : L) :
    V ≃ Private b l ⊕ Shared b l ⊕ Outside b l where
  toFun x := if h : b x={l} then .inl ⟨x,h⟩ else
    if h' : l∈b x then .inr (.inl ⟨x,h',h⟩) else .inr (.inr ⟨x,h'⟩)
  invFun := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  left_inv x := by dsimp only; split_ifs <;> rfl
  right_inv x := by
    rcases x with x | (x | x)
    · simp [x.property]
    · simp [x.property.1,x.property.2]
    · have hx : b x.val≠{l} := by intro h; exact x.property (by simp [h])
      simp [hx,x.property]

def LeafAt (b : V → Finset L) (l p : L) : Prop :=
  ∀ x,l∈b x → b x={l} ∨ b x={l,p}

omit [Fintype V] [Fintype L] [DecidableEq V] in
lemma splitLeaf_bags [Fintype V] [Fintype L] [DecidableEq V]
    (b : V → Finset L) (l p : L) (h : LeafAt b l p) (x : V) :
    leafBags l p (fun y : Outside b l => b y.val) (splitLeaf b l x)=b x := by
  classical
  unfold splitLeaf
  simp only [Equiv.coe_fn_mk]
  split_ifs with he hm
  · exact he.symm
  · exact ((h x hm).resolve_left he).symm
  · rfl

theorem tree_leaf_elimination (b : V → Finset L) (l p : L) (hlp : l≠p)
    (h : LeafAt b l p) (w : L → ℕ → ℕ) :
    assignmentPartition b w =
      assignmentPartition (fun x : Outside b l => b x.val)
        (leafUpdate (Fintype.card (Private b l)) (Fintype.card (Shared b l)) l p w) := by
  classical
  rw [assignmentPartition_equiv b _ (splitLeaf b l) (splitLeaf_bags b l p h)]
  exact leaf_elimination l p hlp _ (fun x => x.property) w

def rootBags {U : Type*} (l : L) (b : W → Finset L) : U ⊕ W → Finset L :=
  Sum.elim (fun _ => {l}) b

noncomputable def rootAssignmentEquiv {U : Type*} [Fintype U] [DecidableEq U]
    (l : L) (b : W → Finset L) : Assignment (rootBags (U:=U) l b) ≃ Assignment b where
  toFun f := ⟨fun x => f.val (.inr x),fun x => f.property _⟩
  invFun f := ⟨Sum.elim (fun _ => l) f.val,by
    intro x; rcases x with x | x
    · simp [rootBags]
    · exact f.property x⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rcases x with x | x
    · have h := f.property (.inl x)
      have hx : f.val (.inl x)=l := by simpa [rootBags] using h
      exact hx.symm
    · rfl
  right_inv f := rfl

noncomputable def rootUpdate (u : ℕ) (l : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if a=l then w l u else w a r

lemma root_elimination {U : Type*} [Fintype U] [DecidableEq U]
    (l : L) (b : W → Finset L) (hb : ∀ x,l∉b x) (w : L → ℕ → ℕ) :
    assignmentPartition (rootBags (U:=U) l b) w =
      assignmentPartition b (rootUpdate (Fintype.card U) l w) := by
  classical
  unfold assignmentPartition
  apply Fintype.sum_equiv (rootAssignmentEquiv l b)
  intro f
  have hl : fiberCount f.val l = Fintype.card U := by
    rw [fiberCount_sum]
    have he : (fun x : U => f.val (.inl x))=(fun _ => l) := by
      funext x; simpa [rootBags] using f.property (.inl x)
    rw [he,fiberCount_const,ite_eq_left rfl]
    have hz : fiberCount (fun x : W => f.val (.inr x)) l=0 := by
      apply fiberCount_zero
      intro x hx
      exact hb x (hx ▸ f.property (.inr x))
    omega
  apply prod_congr rfl
  intro a ha
  by_cases h : a=l
  · subst a; simp [rootUpdate,hl]
  · simp only [rootUpdate,ite_eq_right h]
    congr 1
    rw [fiberCount_sum]
    have he : (fun x : U => f.val (.inl x))=(fun _ => l) := by
      funext x; simpa [rootBags] using f.property (.inl x)
    rw [he,fiberCount_const,ite_eq_right (Ne.symm h),zero_add]
    rfl

noncomputable def splitRoot (b : V → Finset L) (l : L) :
    V ≃ {x : V // l∈b x} ⊕ Outside b l where
  toFun x := if h : l∈b x then .inl ⟨x,h⟩ else .inr ⟨x,h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv x := by dsimp only; split_ifs <;> rfl
  right_inv x := by rcases x with x | x <;> simp [x.property]

theorem tree_root_elimination (b : V → Finset L) (l : L)
    (h : ∀ x,l∈b x → b x={l}) (w : L → ℕ → ℕ) :
    assignmentPartition b w =
      assignmentPartition (fun x : Outside b l => b x.val)
        (rootUpdate (Fintype.card {x : V // l∈b x}) l w) := by
  classical
  have he (x : V) : rootBags l (fun y : Outside b l => b y.val) (splitRoot b l x)=b x := by
    unfold splitRoot
    simp only [Equiv.coe_fn_mk]
    split_ifs with hx
    · exact (h x hx).symm
    · rfl
  rw [assignmentPartition_equiv b _ (splitRoot b l) he]
  exact root_elimination l _ (fun x => x.property) w

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

noncomputable def activePartition (b : V → Finset L) (R : Finset V) (w : L → ℕ → ℕ) : ℕ :=
  assignmentPartition (fun x : R => b x.val) w

def trim (b : V → Finset L) (R : Finset V) (l : L) : Finset V := R.filter fun x => l∉b x

def privateCount (b : V → Finset L) (R : Finset V) (l : L) : ℕ :=
  (R.filter fun x => b x={l}).card

def sharedCount (b : V → Finset L) (R : Finset V) (l : L) : ℕ :=
  (R.filter fun x => l∈b x ∧ b x≠{l}).card

noncomputable def activeFilterEquiv (R : Finset V) (P : V → Prop) [DecidablePred P] :
    {x : R // P x.val} ≃ (R.filter P) where
  toFun x := ⟨x.val.val,mem_filter.mpr ⟨x.val.property,x.property⟩⟩
  invFun x := ⟨⟨x.val,(mem_filter.mp x.property).1⟩,(mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] in
lemma active_card_filter [Fintype V] [DecidableEq V]
    (R : Finset V) (P : V → Prop) [DecidablePred P] :
    Fintype.card {x : R // P x.val}=(R.filter P).card := by
  rw [Fintype.card_congr (activeFilterEquiv R P),Fintype.card_coe]

omit [Fintype V] in
lemma active_outside [Fintype V]
    (b : V → Finset L) (R : Finset V) (l : L) (w : L → ℕ → ℕ) :
    assignmentPartition (fun x : Outside (fun y : R => b y.val) l => b x.val.val) w =
      activePartition b (trim b R l) w := by
  change assignmentPartition (fun x : {y : R // l∉b y.val} => b x.val.val) w =
    assignmentPartition (fun x : R.filter (fun y => l∉b y) => b x.val) w
  apply assignmentPartition_equiv _ _ (activeFilterEquiv R (fun x => l∉b x))
  intro x
  rfl

theorem active_leaf_elimination (b : V → Finset L) (R : Finset V) (l p : L) (hlp : l≠p)
    (h : LeafAt (fun x : R => b x.val) l p) (w : L → ℕ → ℕ) :
    activePartition b R w = activePartition b (trim b R l)
      (leafUpdate (privateCount b R l) (sharedCount b R l) l p w) := by
  unfold activePartition
  rw [tree_leaf_elimination _ l p hlp h,active_outside]
  rw [show Fintype.card (Private (fun x : R => b x.val) l)=privateCount b R l from
    active_card_filter R (fun x => b x={l}),
    show Fintype.card (Shared (fun x : R => b x.val) l)=sharedCount b R l from
    active_card_filter R (fun x => l∈b x ∧ b x≠{l})]
  rfl

lemma active_root_elimination (b : V → Finset L) (R : Finset V) (l : L)
    (h : ∀ x : R,l∈b x.val → b x.val={l}) (w : L → ℕ → ℕ) :
    activePartition b R w = activePartition b (trim b R l)
      (rootUpdate ((R.filter fun x => l∈b x).card) l w) := by
  unfold activePartition
  rw [tree_root_elimination _ l h,active_outside,active_card_filter R (fun x => l∈b x)]
  rfl

lemma partition_isEmpty {W : Type*} [Fintype W] [DecidableEq W] [IsEmpty W]
    (b : W → Finset L) (w : L → ℕ → ℕ) : assignmentPartition b w=∏ l,w l 0 := by
  classical
  let : Unique (Assignment b) :=
    { default := ⟨isEmptyElim,fun x => isEmptyElim x⟩
      uniq := fun f => Subtype.ext (by funext x; exact isEmptyElim x) }
  simp [assignmentPartition,fiberCount]

omit [Fintype V] in
lemma active_empty [Fintype V] (b : V → Finset L) (w : L → ℕ → ℕ) :
    activePartition b ∅ w=∏ l,w l 0 := partition_isEmpty _ _

def RankedBags (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L) : Prop :=
  ∀ x a,a ∈ b x → ∀ a'∈b x,a≠a' →
    (rank a<rank a' ∧ parent a'=some a) ∨ (rank a'<rank a ∧ parent a=some a')

noncomputable def advanceTable (b : V → Finset L) (R : Finset V) (parent : L → Option L)
    (l : L) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  match parent l with
  | some p => leafUpdate (privateCount b R l) (sharedCount b R l) l p w
  | none => rootUpdate ((R.filter fun x => l∈b x).card) l w

noncomputable def tableDP (b : V → Finset L) (parent : L → Option L) :
    List L → Finset V → (L → ℕ → ℕ) → (L → ℕ → ℕ)
  | [],_,w => w
  | l::ls,R,w => tableDP b parent ls (trim b R l) (advanceTable b R parent l w)

def LegalPlan (b : V → Finset L) (parent : L → Option L) : List L → Finset V → Prop
  | [],R => R=∅
  | l::ls,R =>
    (match parent l with
      | some p => l≠p ∧ LeafAt (fun x : R => b x.val) l p
      | none => ∀ x : R,l∈b x.val → b x.val={l}) ∧
    LegalPlan b parent ls (trim b R l)

theorem tableDP_correct (b : V → Finset L) (parent : L → Option L)
    (ls : List L) (R : Finset V) (hp : LegalPlan b parent ls R) (w : L → ℕ → ℕ) :
    activePartition b R w=∏ l,tableDP b parent ls R w l 0 := by
  induction ls generalizing R w with
  | nil =>
    have hR : R=∅ := hp
    subst R
    exact active_empty b w
  | cons l ls ih =>
    have ht : activePartition b R w =
        activePartition b (trim b R l) (advanceTable b R parent l w) := by
      cases hpar : parent l with
      | none =>
        unfold advanceTable; rw [hpar]
        exact active_root_elimination b R l (by simpa only [LegalPlan,hpar] using hp.1) w
      | some p =>
        have h := hp.1
        simp only [hpar] at h
        unfold advanceTable; rw [hpar]
        exact active_leaf_elimination b R l p h.1 h.2 w
    rw [ht]
    exact ih _ hp.2 _

omit [Fintype V] [Fintype L] [DecidableEq V] in
theorem rank_order_legal [Fintype V] [Fintype L] [DecidableEq V]
    (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags b rank parent)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (ls : List L) (hs : ls.Pairwise (fun a a' => rank a'≤rank a))
    (R : Finset V) (hne : ∀ x∈R,(b x).Nonempty)
    (hc : ∀ x∈R,∀ a∈b x,a∈ls) : LegalPlan b parent ls R := by
  induction ls generalizing R with
  | nil =>
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨a,ha⟩ := hne x hx
    exact List.not_mem_nil (hc x hx a ha)
  | cons l ls ih =>
    have hs' := List.pairwise_cons.mp hs
    have hmax (x : R) (a : L) (ha : a∈b x.val) : rank a≤rank l := by
      have h := hc x.val x.property a ha
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ le_rfl
      · exact hs'.1 a h
    have hparent (x : R) (hl : l∈b x.val) (a : L) (ha : a∈b x.val) (hal : a≠l) :
        parent l=some a := by
      rcases hb x.val l hl a ha (Ne.symm hal) with h | h
      · exact (Nat.not_lt_of_ge (hmax x a ha) h.1).elim
      · exact h.2
    constructor
    · cases hpar : parent l with
      | none =>
        intro x hl
        apply eq_singleton_iff_unique_mem.mpr
        exact ⟨hl,fun a ha => by
          by_contra hal
          have h := hparent x hl a ha hal
          rw [hpar] at h
          cases h⟩
      | some p =>
        constructor
        · intro h; subst p
          exact Nat.lt_irrefl _ (hp l l hpar)
        · intro x hl
          by_cases h : b x.val={l}
          · exact Or.inl h
          · right
            apply Subset.antisymm
            · intro a ha
              by_cases hal : a=l
              · simp [hal]
              · have hpa : p=a := Option.some.inj (hpar.symm.trans (hparent x hl a ha hal))
                simp [hpa]
            · intro a ha
              simp only [mem_insert,mem_singleton] at ha
              rcases ha with ha | ha
              · simpa [ha] using hl
              · rw [ha]
                by_contra hpn
                apply h
                apply eq_singleton_iff_unique_mem.mpr
                refine ⟨hl,fun a ha => ?_⟩
                by_contra hal
                have hpa : p=a := Option.some.inj (hpar.symm.trans (hparent x hl a ha hal))
                exact hpn (hpa ▸ ha)
    · apply ih hs'.2
      · intro x hx
        exact hne x (mem_filter.mp hx).1
      · intro x hx a ha
        have hx' := mem_filter.mp hx
        have h := hc x hx'.1 a ha
        rcases List.mem_cons.mp h with hh | hh
        · exact (hx'.2 (hh ▸ ha)).elim
        · exact hh

end MatchingFPRAS.UnitRefresh

end OAI
