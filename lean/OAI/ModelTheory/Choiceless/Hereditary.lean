import OAI.ModelTheory.Choiceless.Flows

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF

@[simp] theorem mk_out (x : HF A) : mk (Quotient.out x) = x := Quotient.out_eq x

@[simp] theorem isSet_mk (l : Lists A) : isSet (mk l) = l.1 := rfl

@[simp] theorem isSet_atom (a : A) : isSet (atom a) = false := rfl

@[simp] theorem elements_mk (l : Lists A) : elements (mk l) = rawElements l := rfl

@[simp] theorem elements_atom (a : A) : elements (atom a) = ∅ := by
  classical
  change rawElements (Lists.atom a) = ∅
  simp [rawElements, Lists.toList]

@[simp] theorem not_mem_atom (x : HF A) (a : A) : ¬ x ∈ atom a := by
  change ¬ x ∈ elements (atom a)
  simp

theorem atom_injective : Function.Injective (atom : A → HF A) := by
  intro a b h
  have h' := Lists.equiv_atom.mp (mk_eq_mk.mp h)
  cases h'
  rfl

@[simp] theorem isSet_ofFinset (s : Finset (HF A)) : isSet (ofFinset s) = true := rfl

@[simp] theorem elements_ofFinset (s : Finset (HF A)) : elements (ofFinset s) = s := by
  classical
  ext x
  simp only [ofFinset, elements_mk, rawElements, Lists.to_ofList, Finset.mem_image,
    List.mem_toFinset]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨l, ⟨y,hy,rfl⟩,h⟩
    rw [mk_out] at h
    exact h ▸ hy
  · intro hx
    exact ⟨Quotient.out x, ⟨x,hx,rfl⟩, mk_out x⟩

@[simp] theorem mem_ofFinset (x : HF A) (s : Finset (HF A)) : x ∈ ofFinset s ↔ x ∈ s := by
  change x ∈ elements (ofFinset s) ↔ x ∈ s
  rw [elements_ofFinset]

theorem ext_sets {x y : HF A} (hx : isSet x = true) (hy : isSet y = true)
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ l =>
    induction y using Quotient.inductionOn with
    | _ r =>
      rcases l with ⟨(_ | _), l⟩ <;> (try cases hx)
      rcases r with ⟨(_ | _), r⟩ <;> (try cases hy)
      apply mk_eq_mk.mpr
      apply Lists.Equiv.antisymm
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' r)).mp
        apply (h (mk a)).mp
        exact (mem_mk a (Lists.of' l)).mpr ⟨a,ha,Lists.Equiv.refl a⟩
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' l)).mp
        apply (h (mk a)).mpr
        exact (mem_mk a (Lists.of' r)).mpr ⟨a,ha,Lists.Equiv.refl a⟩

theorem ofFinset_elements {x : HF A} (hx : isSet x = true) : ofFinset (elements x) = x := by
  apply ext_sets (isSet_ofFinset _) hx
  intro z
  rw [mem_ofFinset]
  rfl

theorem atom_or_set (x : HF A) : (∃ a, x = atom a) ∨ x = ofFinset (elements x) := by
  induction x using Quotient.inductionOn with
  | _ l =>
    rcases l with ⟨(_ | _), l⟩
    · cases l with
      | atom a => exact Or.inl ⟨a,rfl⟩
    · exact Or.inr (ofFinset_elements rfl).symm

@[simp] theorem rank_mk (l : Lists A) : rank (mk l) = rawRank l := rfl

@[simp] theorem rank_atom (a : A) : rank (atom a) = 0 := rfl

theorem mem_wellFounded : WellFounded (fun x y : HF A => x ∈ y) :=
  (measure rank).wf.mono (fun _ _ h => rank_lt_of_mem h)

def rawMap' (f : A → B) : {b : Bool} → Lists' A b → Lists' B b
  | _, .atom a => .atom (f a)
  | _, .nil => .nil
  | _, .cons' a l => .cons' (rawMap' f a) (rawMap' f l)

def rawMap (f : A → B) (l : Lists A) : Lists B := ⟨l.1, rawMap' f l.2⟩

theorem toList_rawMap' (f : A → B) {b : Bool} (l : Lists' A b) :
    (rawMap' f l).toList = l.toList.map (rawMap f) := by
  induction l with
  | atom => rfl
  | nil => rfl
  | cons' a l iha ihl => simp only [rawMap', Lists'.toList, ihl]; rfl

theorem rawMap_congr (f : A → B) {l r : Lists A} (h : Lists.Equiv l r) :
    Lists.Equiv (rawMap f l) (rawMap f r) := by
  induction h using Lists.Equiv.rec
      (motive_2 := fun l r _ => Lists'.Subset (rawMap' f l) (rawMap' f r)) with
  | refl => exact Lists.Equiv.refl _
  | antisymm hl hr ihl ihr => exact Lists.Equiv.antisymm ihl ihr
  | nil => exact Lists'.Subset.nil
  | @cons a a' l r heq hmem hsub iheq ihsub =>
    apply Lists'.Subset.cons iheq _ ihsub
    rw [toList_rawMap']
    exact List.mem_map.mpr ⟨a',hmem,rfl⟩

def map (f : A → B) (x : HF A) : HF B :=
  Quotient.liftOn x (fun l => mk (rawMap f l)) (fun _ _ h => mk_eq_mk.mpr (rawMap_congr f h))

@[simp] theorem map_mk (f : A → B) (l : Lists A) : map f (mk l) = mk (rawMap f l) := rfl

@[simp] theorem map_atom (f : A → B) (a : A) : map f (atom a) = atom (f a) := rfl

@[simp] theorem isSet_map (f : A → B) (x : HF A) : isSet (map f x) = isSet x := by
  induction x using Quotient.inductionOn with
  | _ l => rfl

theorem elements_map (f : A → B) (x : HF A) :
    elements (map f x) = (elements x).image (map f) := by
  classical
  induction x using Quotient.inductionOn with
  | _ l =>
    change (rawMap f l).toList.toFinset.image mk =
      (l.toList.toFinset.image mk).image (map f)
    rw [Finset.image_image]
    have ht : (rawMap f l).toList = l.toList.map (rawMap f) := toList_rawMap' f l.2
    rw [ht]
    ext z
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩
      exact ⟨a,ha,h⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨rawMap f a,⟨a,ha,rfl⟩,h⟩

@[simp] theorem map_ofFinset (f : A → B) (s : Finset (HF A)) :
    map f (ofFinset s) = ofFinset (s.image (map f)) := by
  classical
  apply ext_sets (by simp) (by simp)
  intro z
  change z ∈ elements (map f (ofFinset s)) ↔ z ∈ elements (ofFinset (s.image (map f)))
  rw [elements_map, elements_ofFinset, elements_ofFinset]

@[simp] theorem rawMap_id : ∀ l : Lists A, rawMap id l = l := by
  rintro ⟨b,l⟩
  have h : rawMap' id l = l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_id (x : HF A) : map id x = x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map id (mk l) = mk l
    rw [map_mk, rawMap_id]

theorem rawMap_comp {C : Type*} (g : B → C) (f : A → B) (l : Lists A) :
    rawMap g (rawMap f l) = rawMap (g ∘ f) l := by
  rcases l with ⟨b,l⟩
  have h : rawMap' g (rawMap' f l) = rawMap' (g ∘ f) l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_comp {C : Type*} (g : B → C) (f : A → B) (x : HF A) :
    map g (map f x) = map (g ∘ f) x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map g (map f (mk l)) = map (g ∘ f) (mk l)
    simp only [map_mk,rawMap_comp]

def mapEquiv (e : A ≃ B) : HF A ≃ HF B where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    rw [map_comp]
    have h : (e.symm : B → A) ∘ (e : A → B) = id := by funext a; simp
    rw [h,map_id]
  right_inv x := by
    rw [map_comp]
    have h : (e : A → B) ∘ (e.symm : B → A) = id := by funext a; simp
    rw [h,map_id]

instance {G : Type*} [Group G] [MulAction G A] : MulAction G (HF A) where
  smul g x := map (fun a => g • a) x
  one_smul x := by
    change map (fun a : A => (1 : G) • a) x = x
    have h : (fun a : A => (1 : G) • a) = id := by funext a; simp
    rw [h,map_id]
  mul_smul g h x := by
    change map (fun a : A => (g*h) • a) x = map (fun a => g • a) (map (fun a => h • a) x)
    rw [map_comp]
    congr 1
    funext a
    exact mul_smul g h a

@[simp] theorem smul_atom {G : Type*} [Group G] [MulAction G A] (g : G) (a : A) :
    g • atom a = atom (g • a) := rfl

@[simp] theorem smul_ofFinset {G : Type*} [Group G] [MulAction G A] (g : G) (s : Finset (HF A)) :
    g • ofFinset s = ofFinset (s.image (fun x => g • x)) := map_ofFinset _ _

def Supports {G : Type*} [Group G] [MulAction G A] {k : ℕ}
    (alpha : Fin k → A) (x : HF A) : Prop :=
  ∀ g : G, (∀ i, g • alpha i = alpha i) → g • x = x

def Supported {G : Type*} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∃ alpha : Fin s → A, Supports (G := G) alpha x

def HereditarilySupported {G : Type*} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∀ y, Relation.ReflTransGen (fun a b : HF A => a ∈ b) y x → Supported (G := G) s y

end CPTSeparation.Hereditary

namespace CPTSeparation.Forms

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

inductive Form (J L : Type*)
  | atom (j : J)
  | set (n : ℕ) (child : Fin n → Form J L) (label : Fin n → L)

namespace Form

variable [finiteI : Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A]

def value (S : Structure R A) (e : J ⊕ J ↪ I) :
    Form J (Set (Formula R I)) → (J → A) → HF A
  | .atom j, a => Hereditary.atom (a j)
  | .set _ child label, a => Hereditary.ofFinset
      (Finset.univ.biUnion fun i =>
        (Finset.univ.filter fun b : J → A =>
          tupleType S e (Sum.elim b a) = label i).image (value S e (child i)))

omit R I J A in
@[simp] theorem value_atom.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I) (j : J) (a : J → A) :
    value S e (.atom j) a = Hereditary.atom (a j) := rfl

omit R I J A in
@[simp] theorem value_set_isSet.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) : isSet (value S e (.set n child label) a) = true := rfl

omit R I J A in
@[simp] theorem mem_value_set.{uDecl1, uDecl2, uDecl3, uDecl4}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) (x : HF A) :
    x ∈ value S e (.set n child label) a ↔
      ∃ i b, tupleType S e (Sum.elim b a) = label i ∧ value S e (child i) b = x := by
  classical
  simp only [value,mem_ofFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_filter,true_and]

omit R I J A B in
theorem value_iso.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {J : Type uDecl3}
    {A : Type uDecl4}
    {B : Type uDecl5}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A] [Fintype B] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I) (f : A ≃ B)
    (hf : ∀ r a b, S.rel r a b ↔ T.rel r (f a) (f b))
    (φ : Form J (Set (Formula R I))) (a : J → A) :
    Hereditary.map f (value S e φ a) = value T e φ (f ∘ a) := by
  induction φ generalizing a with
  | atom j => rfl
  | set n child label ih =>
    apply Hereditary.ext_sets (by simp [value]) (by simp)
    intro x
    change x ∈ elements (Hereditary.map f (value S e (.set n child label) a)) ↔ _
    rw [Hereditary.elements_map]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e n child label a y).mp hy
      apply (mem_value_set T e n child label (f ∘ a) _).mpr
      refine ⟨i,f ∘ b,?_,(ih i b).symm⟩
      have heq : Sum.elim (f ∘ b) (f ∘ a) = f ∘ Sum.elim b a := by
        funext j; cases j <;> rfl
      rw [heq,← tupleType_iso S T e f hf,ht]
    · intro hx
      obtain ⟨i,b,ht,hx⟩ := (mem_value_set T e n child label (f ∘ a) x).mp hx
      let c := f.symm ∘ b
      have hc : f ∘ c = b := by funext j; simp [c]
      refine ⟨value S e (child i) c,?_,?_⟩
      · apply (mem_value_set S e n child label a _).mpr
        refine ⟨i,c,?_,rfl⟩
        rw [tupleType_iso S T e f hf]
        have heq : f ∘ Sum.elim c a = Sum.elim b (f ∘ a) := by
          funext j; cases j <;> simp [c]
        rw [heq,ht]
      · rw [ih,hc,hx]

end Form

def cross31 : J ⊕ J ↪ (J ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl j))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross42 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl (Sum.inr j)))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross34 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

theorem swap_type [Fintype J] [DecidableEq I] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I)
    (a b : J → A) (a' b' : J → B)
    (h : tupleType S e (Sum.elim a b) = tupleType T e (Sum.elim a' b')) :
    tupleType S e (Sum.elim b a) = tupleType T e (Sum.elim b' a') := by
  have ht := tupleType_project S T e e (Equiv.sumComm J J).toEmbedding _ _ h
  have h1 : Sum.elim a b ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b a := by
    funext j; cases j <;> rfl
  have h2 : Sum.elim a' b' ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b' a' := by
    funext j; cases j <;> rfl
  simpa only [h1,h2] using ht

@[simp] theorem elim_comp_cross31 (a b c : J → A) :
    Sum.elim (Sum.elim a b) c ∘ cross31 = Sum.elim c a := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross42 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross42 = Sum.elim d b := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross34 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross34 = Sum.elim c d := by
  funext j; cases j <;> rfl

section AtomicTransfer

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

variable (S : Structure R A) (T : Structure R B)

variable (e2 : J ⊕ J ↪ I) (e3 : (J ⊕ J) ⊕ J ↪ I)

variable (e4 : ((J ⊕ J) ⊕ J) ⊕ J ↪ I)

open Form

include e3 e4

private theorem set_subset_transfer
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hsub : ∀ x, x ∈ value S e2 (.set n child label) a →
      x ∈ value S e2 (.set k other lab) b) :
    ∀ x, x ∈ value T e2 (.set n child label) a' →
      x ∈ value T e2 (.set k other lab) b' := by
  intro x hx
  obtain ⟨i,c',hl,rfl⟩ := (mem_value_set T e2 n child label a' x).mp hx
  obtain ⟨c,h3⟩ := tupleType_append T S e2 e3 (Sum.elim a' b') (Sum.elim a b) c' ht.symm
  have hca := tupleType_project T S e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hca
  have hmem : value S e2 (child i) c ∈ value S e2 (.set n child label) a :=
    (mem_value_set S e2 n child label a _).mpr ⟨i,c,hca.symm.trans hl,rfl⟩
  obtain ⟨j,d,hlab,heq⟩ := (mem_value_set S e2 k other lab b _).mp (hsub _ hmem)
  obtain ⟨d',h4⟩ := tupleType_append S T e3 e4 (Sum.elim (Sum.elim a b) c)
    (Sum.elim (Sum.elim a' b') c') d h3.symm
  have hdb := tupleType_project S T e4 e2 cross42 _ _ h4
  have hcd := tupleType_project S T e4 e2 cross34 _ _ h4
  simp only [elim_comp_cross42] at hdb
  simp only [elim_comp_cross34] at hcd
  exact (mem_value_set T e2 k other lab b' _).mpr
    ⟨j,d',hdb.symm.trans hlab,((hc i j c d c' d' hcd).mp heq.symm).symm⟩

private theorem set_eq_forward
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (h : value S e2 (.set n child label) a = value S e2 (.set k other lab) b) :
    value T e2 (.set n child label) a' = value T e2 (.set k other lab) b' := by
  apply Hereditary.ext_sets (by simp) (by simp)
  intro x
  constructor
  · exact set_subset_transfer S T e2 e3 e4 n k child other label lab hc a b a' b' ht
      (fun z hz => by rw [←h]; exact hz) x
  · apply set_subset_transfer S T e2 e3 e4 k n other child lab label
      (fun j i c d c' d' ht' => ?_) b a b' a' (swap_type S T e2 a b a' b' ht)
      (fun z hz => by rw [h]; exact hz) x
    have hh := hc i j d c d' c' (swap_type S T e2 c d c' d' ht')
    exact ⟨fun he => (hh.mp he.symm).symm,fun he => (hh.mpr he.symm).symm⟩

theorem equality_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a = value S e2 ψ b ↔ value T e2 φ a' = value T e2 ψ b' := by
  induction φ generalizing ψ a b a' b' with
  | atom i =>
    cases ψ with
    | atom j =>
      have he := (typeOf_eq_iff S T (tupleNames e2) _ _).mp ht
        (.equal (e2 (.inl i)) (e2 (.inr j))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply,Sum.elim_inl,Sum.elim_inr,
        value_atom,Hereditary.atom_injective.eq_iff] using he
    | set k other lab =>
      have hfalseA : value S e2 (.atom i) a ≠ value S e2 (.set k other lab) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.atom i) a' ≠ value T e2 (.set k other lab) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
  | set n child label ih =>
    cases ψ with
    | atom j =>
      have hfalseA : value S e2 (.set n child label) a ≠ value S e2 (.atom j) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.set n child label) a' ≠ value T e2 (.atom j) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
    | set k other lab =>
      constructor
      · exact set_eq_forward S T e2 e3 e4 n k child other label lab
          (fun i j c d c' d' ht' => ih i (other j) c d c' d' ht') a b a' b' ht
      · exact set_eq_forward T S e2 e3 e4 n k child other label lab
          (fun i j c' d' c d ht' => (ih i (other j) c d c' d' ht'.symm).symm)
          a' b' a b ht.symm

private theorem membership_forward (φ : Form J (Set (Formula R I)))
    (k : ℕ) (other : Fin k → Form J (Set (Formula R I)))
    (lab : Fin k → Set (Formula R I))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hm : value S e2 φ a ∈ value S e2 (.set k other lab) b) :
    value T e2 φ a' ∈ value T e2 (.set k other lab) b' := by
  obtain ⟨i,c,hl,heq⟩ := (mem_value_set S e2 k other lab b _).mp hm
  obtain ⟨c',h3⟩ := tupleType_append S T e2 e3 (Sum.elim b a) (Sum.elim b' a') c
    (swap_type S T e2 a b a' b' ht)
  have hcb := tupleType_project S T e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hcb
  let u : J ⊕ J ↪ (J ⊕ J) ⊕ J :=
    cross31.trans (Function.Embedding.sumMap (Equiv.sumComm J J).toEmbedding
      (Function.Embedding.refl J))
  have hca := tupleType_project S T e3 e2 u _ _ h3
  have hueq (a b c : J → A) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  have hueq' (a b c : J → B) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  rw [hueq,hueq'] at hca
  exact (mem_value_set T e2 k other lab b' _).mpr ⟨i,c',hcb.symm.trans hl,
    (equality_transfer S T e2 e3 e4 (other i) φ c a c' a' hca).mp heq⟩

theorem membership_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a ∈ value S e2 ψ b ↔ value T e2 φ a' ∈ value T e2 ψ b' := by
  cases ψ with
  | atom j => simp
  | set k other lab =>
    exact ⟨membership_forward S T e2 e3 e4 φ k other lab a b a' b' ht,
      membership_forward T S e2 e3 e4 φ k other lab a' b' a b ht.symm⟩

end AtomicTransfer

variable {G : Type*} [Group G] [MulAction G A]

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [nonemptyA : Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

omit R I A G s S e2 hAut in
theorem value_smul.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (g : G) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    g • value S e2 φ a = value S e2 φ (fun i => g • a i) := by
  exact value_iso S S e2 (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm) φ a

omit R I A G s S e2 hAut in
theorem value_supported.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    Supports (G := G) a (value S e2 φ a) := by
  intro g hg
  rw [value_smul S e2 hAut]
  exact congrArg (value S e2 φ) (funext hg)

omit A G s in
private theorem hereditary_mem.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A]
    {s : ℕ} {x y : HF A}
    (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := by
  intro z hz
  exact hx z (hz.trans (Relation.ReflTransGen.single hy))

omit A G s in
private theorem hereditary_intro.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A]
    {s : ℕ} (x : HF A) (hx : Supported (G := G) s x)
    (hm : ∀ y ∈ x, HereditarilySupported (G := G) s y) :
    HereditarilySupported (G := G) s x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | tail hpath hstep => exact hm _ hstep _ hpath

include hAut in
theorem value_hereditarily_supported (φ : Form (Fin s) (Set (Formula R I)))
    (a : Fin s → A) : HereditarilySupported (G := G) s (value S e2 φ a) := by
  induction φ generalizing a with
  | atom i =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    exact (not_mem_atom y (a i) hy).elim
  | set n child label ih =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
    exact ih i b

omit A G in
private theorem smul_mem.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A] (g : G) {x y : HF A} (h : y ∈ x) : g • y ∈ g • x := by
  change Hereditary.map (fun a => g • a) y ∈
    elements (Hereditary.map (fun a => g • a) x)
  let := Hereditary.instDecidableEqHF (A := A)
  rw [elements_map]
  exact Finset.mem_image.mpr ⟨y,h,rfl⟩

include hAut in

omit R I A G s S e2 hAut in
theorem representation.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (hs : 0 < s)
    (hHom : ∀ p q : Fin s ⊕ Fin s → A,
      tupleType S e2 p = tupleType S e2 q → ∃ g : G, ∀ i, g • p i = q i)
    (x : HF A) (hx : HereditarilySupported (G := G) s x) :
    ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, value S e2 φ a = x := by
  induction x using mem_wellFounded.induction with
  | h x ih =>
    rcases atom_or_set x with ⟨b,rfl⟩ | hxset
    · exact ⟨.atom ⟨0,hs⟩,fun _ => b,rfl⟩
    · obtain ⟨a,ha⟩ := hx x Relation.ReflTransGen.refl
      have hr : ∀ y : {y // y ∈ elements x},
          ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ b : Fin s → A,
            value S e2 φ b = y.1 := by
        intro y
        exact ih y.1 y.2 (hereditary_mem hx y.2)
      choose form mol hvalue using hr
      let n := Fintype.card {y // y ∈ elements x}
      let en : Fin n ≃ {y // y ∈ elements x} := (Fintype.equivFin _).symm
      let child : Fin n → Form (Fin s) (Set (Formula R I)) := fun i => form (en i)
      let β : Fin n → Fin s → A := fun i => mol (en i)
      let label : Fin n → Set (Formula R I) := fun i => tupleType S e2 (Sum.elim (β i) a)
      refine ⟨.set n child label,a,?_⟩
      apply Hereditary.ext_sets (by simp) (by rw [hxset]; rfl)
      intro y
      constructor
      · intro hy
        obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
        obtain ⟨g,hg⟩ := hHom (Sum.elim (β i) a) (Sum.elim b a) ht.symm
        have hga : ∀ j, g • a j = a j := fun j => hg (.inr j)
        have hgb : (fun j => g • β i j) = b := funext (fun j => hg (.inl j))
        have hyx : (en i).1 ∈ x := (en i).2
        have hmap := smul_mem g hyx
        rw [ha g hga] at hmap
        have hv : value S e2 (child i) b = g • (en i).1 := by
          rw [←hgb,←value_smul S e2 hAut]
          exact congrArg (fun z : HF A => g • z) (hvalue (en i))
        rw [hv]
        exact hmap
      · intro hy
        let y' : {y // y ∈ elements x} := ⟨y,hy⟩
        let i := en.symm y'
        apply (mem_value_set S e2 n child label a y).mpr
        refine ⟨i,β i,rfl,?_⟩
        have hv := hvalue (en i)
        simpa only [child,β,i,Equiv.apply_symm_apply] using hv

end CPTSeparation.Forms

namespace CPTSeparation.Counting

open Classical

variable {R I J A B : Type*} [DecidableEq I]

def triangular {X Y : Type*} (e : X ≃ Y) (f : X → A ≃ B) : X × A ≃ Y × B where
  toFun p := (e p.1, f p.1 p.2)
  invFun p := (e.symm p.1, (f (e.symm p.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def snocTuple {n : ℕ} (a : Fin n → A) (x : A) : Fin (n+1) → A :=
  Fin.lastCases x a

@[simp] theorem snocTuple_castSucc {n : ℕ} (a : Fin n → A) (x : A) (i : Fin n) :
    snocTuple a x i.castSucc = a i := by simp [snocTuple]

@[simp] theorem snocTuple_last {n : ℕ} (a : Fin n → A) (x : A) :
    snocTuple a x (Fin.last n) = x := by simp [snocTuple]

def snocEquiv (n : ℕ) : (Fin (n+1) → A) ≃ (Fin n → A) × A where
  toFun a := (fun i => a i.castSucc, a (Fin.last n))
  invFun p := snocTuple p.1 p.2
  left_inv a := by
    funext i
    induction i using Fin.lastCases <;> simp
  right_inv p := by ext <;> simp

def appendPosition (J : Type*) (n : ℕ) : (J ⊕ Fin n) ⊕ Unit ≃ J ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr i.castSucc)) (fun _ => Sum.inr (Fin.last n))
  invFun := Sum.elim (fun j => Sum.inl (Sum.inl j))
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))
  left_inv p := by rcases p with (j|i)|u <;> simp
  right_inv p := by
    rcases p with j|i
    · rfl
    · induction i using Fin.lastCases <;> simp

variable [Fintype I] [Fintype J] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append_one_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ Unit ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : A ≃ B, ∀ x, tupleType S E (Sum.elim a (fun _ => x)) =
      tupleType T E (Sum.elim b (fun _ => f x)) := by
  let ep := Function.Embedding.inl.trans E
  let i := E (Sum.inr ())
  have hp := tupleType_project S T e ep (Function.Embedding.refl J) a b ht
  change tupleType S ep a = tupleType T ep b at hp
  have hi : i ∉ tupleNames ep := by
    rintro hh
    obtain ⟨j,hj⟩ := (mem_tupleNames ep i).mp hh
    have hh := E.injective hj
    cases hh
  have hn : insert i (tupleNames ep) = tupleNames E := by
    ext p
    simp only [Finset.mem_insert,mem_tupleNames]
    constructor
    · rintro (rfl|⟨j,rfl⟩)
      · exact ⟨Sum.inr (),rfl⟩
      · exact ⟨Sum.inl j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases j with j|u
      · exact Or.inr ⟨j,rfl⟩
      · cases u; exact Or.inl rfl
  have ha (x : A) : tupleType S E (Sum.elim a (fun _ => x)) =
      typeOf S (tupleNames E) (Function.update (tupleAssignment ep a) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep a j
    · cases u; simp [i]
  have hb (x : B) : tupleType T E (Sum.elim b (fun _ => x)) =
      typeOf T (tupleNames E) (Function.update (tupleAssignment ep b) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep b j
    · cases u; simp [i]
  obtain ⟨f,hf⟩ := extension_bijection S T (tupleNames ep) i hi
    (tupleAssignment ep a) (tupleAssignment ep b) hp
  refine ⟨f,fun x => ?_⟩
  rw [ha,hb]
  simpa only [hn] using hf x

theorem tupleType_append_fin_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (n : ℕ) (E : J ⊕ Fin n ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (Fin n → A) ≃ (Fin n → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  induction n with
  | zero =>
    let f : (Fin 0 → A) ≃ (Fin 0 → B) :=
      ⟨fun _ => Fin.elim0,fun _ => Fin.elim0,
        fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩
    refine ⟨f,fun c => ?_⟩
    let u : J ⊕ Fin 0 ↪ J :=
      ⟨Sum.elim id Fin.elim0,by
        intro x y h
        rcases x with x|x
        · rcases y with y|y
          · exact congrArg Sum.inl h
          · exact Fin.elim0 y
        · exact Fin.elim0 x⟩
    have h := tupleType_project S T e E u a b ht
    have ha : a ∘ u = Sum.elim a c := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    have hb : b ∘ u = Sum.elim b (f c) := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    simpa only [ha,hb] using h
  | succ n ih =>
    let pre : J ⊕ Fin n ↪ J ⊕ Fin (n+1) :=
      Function.Embedding.sumMap (Function.Embedding.refl J) Fin.castSuccEmb
    let ep := pre.trans E
    obtain ⟨f,hf⟩ := ih ep
    let E1 := (appendPosition J n).toEmbedding.trans E
    have h1 (c : Fin n → A) : ∃ g : A ≃ B, ∀ x,
        tupleType S E1 (Sum.elim (Sum.elim a c) (fun _ => x)) =
        tupleType T E1 (Sum.elim (Sum.elim b (f c)) (fun _ => g x)) :=
      tupleType_append_one_bijection S T ep E1 _ _ (hf c)
    choose g hg using h1
    let F := (snocEquiv (A:=A) n).trans
      ((triangular f g).trans (snocEquiv (A:=B) n).symm)
    refine ⟨F,fun c => ?_⟩
    have hh := tupleType_project S T E1 E (appendPosition J n).symm.toEmbedding
      _ _ (hg (fun i => c i.castSucc) (c (Fin.last n)))
    have ha : (Sum.elim (Sum.elim a (fun i => c i.castSucc))
        (fun _ => c (Fin.last n))) ∘ (appendPosition J n).symm = Sum.elim a c := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;> simp [appendPosition]
    have hb : (Sum.elim (Sum.elim b (f (fun i => c i.castSucc)))
        (fun _ => g (fun i => c i.castSucc) (c (Fin.last n)))) ∘
        (appendPosition J n).symm = Sum.elim b (F c) := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;>
          simp [appendPosition,F,snocEquiv,triangular,snocTuple]
    simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_append_bijection {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (D → A) ≃ (D → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  let en := Fintype.equivFin D
  let E' := (Equiv.sumCongr (Equiv.refl J) en.symm).toEmbedding.trans E
  obtain ⟨f,hf⟩ := tupleType_append_fin_bijection S T e (Fintype.card D) E' a b ht
  let F := (Equiv.arrowCongr en (Equiv.refl A)).trans
    (f.trans (Equiv.arrowCongr en.symm (Equiv.refl B)))
  refine ⟨F,fun c => ?_⟩
  have hh := tupleType_project S T E' E
    (Equiv.sumCongr (Equiv.refl J) en).toEmbedding _ _ (hf (c ∘ en.symm))
  have ha : (Sum.elim a (c ∘ en.symm)) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim a c := by
    funext j; rcases j with j|j <;> simp
  have hb : (Sum.elim b (f (c ∘ en.symm))) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim b (F c) := by
    funext j; rcases j with j|j <;> rfl
  simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_extension_equiv {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) (τ : Set (Formula R I)) :
    Nonempty ({c : D → A // tupleType S E (Sum.elim a c) = τ} ≃
      {d : D → B // tupleType T E (Sum.elim b d) = τ}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T e E a b ht
  exact ⟨f.subtypeEquiv (fun c => by rw [hf c])⟩

end CPTSeparation.Counting

end

end OAI
