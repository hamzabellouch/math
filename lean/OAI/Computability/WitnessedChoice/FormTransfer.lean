import OAI.Computability.WitnessedChoice.SupportedForms

namespace OAI


namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

abbrev Domain (G : Type*) [Group G] [MulAction G A] (s : ℕ) :=
  {x : HF A // HereditarilySupported (G := G) s x}

def Cell (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Set (Domain (A := A) G s) :=
  {x | x.1 ∈ labelValues S ep e2 p τ φ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def cellEquiv (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Cell (G := G) S ep e2 p φ τ ≃ labelValues S ep e2 p τ φ :=
  Equiv.subtypeSubtypeEquivSubtype
    (p := HereditarilySupported (G := G) s)
    (q := fun x => x ∈ labelValues S ep e2 p τ φ) (fun hx => by
    obtain ⟨a,rfl⟩ := hx
    exact value_hereditarily_supported S e2 hAutA φ a.1)

include hAutA in
omit [Fintype I] in
private theorem cell_finite (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    (Cell (G := G) S ep e2 p φ τ).Finite := by
  let := Fintype.ofEquiv (labelValues S ep e2 p τ φ) (cellEquiv S ep e2 hAutA p φ τ).symm
  exact Set.toFinite _

include hAutA hAutB epp e3 e4 in




theorem supported_domain_bijection (hs : 0 < s) (e0 : P ↪ I)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (hp : tupleType S e0 p = tupleType T e0 q) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, ∃ b : Fin s → B,
        Form.value S e2 φ a = x.1 ∧ Form.value T e2 φ b = (f x).1 ∧
        tupleType S ep (Sum.elim p a) = tupleType T ep (Sum.elim q b) := by
  let L := {l : Form (Fin s) (Set (Formula R I)) × Set (Formula R I) //
    Nonempty (Molecules S ep p l.2)}
  let C : L → Set (Domain (A := A) G s) := fun l => Cell S ep e2 p l.1.1 l.1.2
  let D : L → Set (Domain (A := B) H s) := fun l => Cell T ep e2 q l.1.1 l.1.2
  have nonemptyB (l : L) : Nonempty (Molecules T ep q l.1.2) := by
    obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp l.1.2
    exact Nonempty.map f l.2
  have coverC : ∀ x, ∃ l, x ∈ C l := by
    intro x
    obtain ⟨φ,a,ha⟩ := representation S e2 hAutA hs hHomA2 x.1 x.2
    let τ := tupleType S ep (Sum.elim p a)
    let l : L := ⟨(φ,τ),⟨⟨a,rfl⟩⟩⟩
    exact ⟨l,⟨⟨a,rfl⟩,ha⟩⟩
  have coverD : ∀ y, ∃ l, y ∈ D l := by
    intro y
    obtain ⟨φ,b,hb⟩ := representation T e2 hAutB hs hHomB2 y.1 y.2
    obtain ⟨a,ha⟩ := tupleType_append T S e0 ep q p b hp.symm
    let τ := tupleType T ep (Sum.elim q b)
    let l : L := ⟨(φ,τ),⟨⟨a,ha.symm⟩⟩⟩
    exact ⟨l,⟨⟨b,rfl⟩,hb⟩⟩
  have partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k := by
    intro l k x hx hk
    have hh := label_partition S ep e2 hAutA p l.1.2 hHomA l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF A) => {x : Domain G s | x.1 ∈ Z}) hh
  have partD : ∀ l k x, x ∈ D l → x ∈ D k → D l = D k := by
    intro l k x hx hk
    have hh := label_partition T ep e2 hAutB q l.1.2 hHomB l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF B) => {x : Domain H s | x.1 ∈ Z}) hh
  have same : ∀ l k, C l = C k ↔ D l = D k := by
    intro l k
    constructor
    · intro he
      obtain ⟨a⟩ := l.2
      let x : Domain G s := ⟨Form.value S e2 l.1.1 a.1,
        value_hereditarily_supported S e2 hAutA _ _⟩
      have hx : x ∈ C l := ⟨a,rfl⟩
      have hk : x ∈ C k := he ▸ hx
      obtain ⟨y,hy,hy'⟩ := label_overlap_transfer S T ep epp e2 e3 e4 e0 p q hp
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨x.1,hx,hk⟩
      have hsupp : HereditarilySupported (G := H) s y := by
        obtain ⟨b,rfl⟩ := hy
        exact value_hereditarily_supported T e2 hAutB _ _
      exact partD l k ⟨y,hsupp⟩ hy hy'
    · intro he
      obtain ⟨b⟩ := nonemptyB l
      let y : Domain H s := ⟨Form.value T e2 l.1.1 b.1,
        value_hereditarily_supported T e2 hAutB _ _⟩
      have hy : y ∈ D l := ⟨b,rfl⟩
      have hk : y ∈ D k := he ▸ hy
      obtain ⟨x,hx,hx'⟩ := label_overlap_transfer T S ep epp e2 e3 e4 e0 q p hp.symm
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨y.1,hy,hk⟩
      have hsupp : HereditarilySupported (G := G) s x := by
        obtain ⟨a,rfl⟩ := hx
        exact value_hereditarily_supported S e2 hAutA _ _
      exact partC l k ⟨x,hsupp⟩ hx hx'
  have card : ∀ l, Nat.card (C l) = Nat.card (D l) := by
    intro l
    obtain ⟨a⟩ := l.2
    obtain ⟨b⟩ := nonemptyB l
    have hh := label_values_card S T ep epp e2 e3 e4 hAutA hAutB hHomA hHomB
      p q l.1.2 l.1.1 a b
    have he := Nat.card_congr (cellEquiv S ep e2 hAutA p l.1.1 l.1.2)
    have hf := Nat.card_congr (cellEquiv T ep e2 hAutB q l.1.1 l.1.2)
    exact he.trans (hh.trans hf.symm)
  obtain ⟨f,hf⟩ := WitnessedSeparation.glue_finite_cells C D coverC coverD partC partD same
    (fun l => cell_finite S ep e2 hAutA p l.1.1 l.1.2)
    (fun l => cell_finite T ep e2 hAutB q l.1.1 l.1.2) card
  refine ⟨f,fun x => ?_⟩
  obtain ⟨l,⟨a,ha⟩,⟨b,hb⟩⟩ := hf x
  exact ⟨l.1.1,a.1,b.1,ha,hb,a.2.trans b.2.symm⟩

end





noncomputable section

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype V] [DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

inductive HFRelation (R : Type*)
  | mem | atom | base (r : R)

def hfStructure (S : Structure R A) : Structure (HFRelation R) (Domain (A := A) G s) where
  rel
    | .mem, x, y => x.1 ∈ y.1
    | .atom, x, _ => isSet x.1 = false
    | .base r, x, y => ∃ a b, x.1 = Hereditary.atom a ∧ y.1 = Hereditary.atom b ∧ S.rel r a b

def Represented (S : Structure R A) (T : Structure R B)
    (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) : Prop :=
  ∃ φ : V → Form (Fin s) (Set (Formula R I)), ∃ a : V × Fin s → A,
    ∃ b : V × Fin s → B,
      (∀ i, Form.value S e2 (φ i) (fun j => a (i,j)) = (v i).1) ∧
      (∀ i, Form.value T e2 (φ i) (fun j => b (i,j)) = (w i).1) ∧
      tupleType S ef a = tupleType T ef b

def twoBlocks (i j : V) (h : i ≠ j) : Fin s ⊕ Fin s ↪ V × Fin s where
  toFun := Sum.elim (Prod.mk i) (Prod.mk j)
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp only [Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq] at hab
    · congr 1; exact hab.2
    · exact (h hab.1).elim
    · exact (h hab.1.symm).elim
    · congr 1; exact hab.2

omit [Fintype A] [Nonempty A] [Fintype V] [DecidableEq V] in
@[simp] theorem comp_twoBlocks (i j : V) (h : i ≠ j) (a : V × Fin s → A) :
    a ∘ twoBlocks i j h = Sum.elim (fun k => a (i,k)) (fun k => a (j,k)) := by
  funext x; cases x <;> rfl

def splitBlock (i : V) : ({j : V // j ≠ i} × Fin s) ⊕ Fin s ≃ V × Fin s where
  toFun := Sum.elim (fun x => (x.1.1,x.2)) (fun j => (i,j))
  invFun := fun x => if h : x.1 = i then .inr x.2 else .inl (⟨x.1,h⟩,x.2)
  left_inv := by
    intro x; cases x with
    | inl x => simp [x.1.2]
    | inr j => simp
  right_inv := by
    intro x; by_cases h : x.1 = i
    · simp [h]; exact Prod.ext h.symm rfl
    · simp [h]

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include e3 e4 in
theorem represented_equal (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : v i = v j ↔ w i = w j := by
  by_cases hij : i = j
  · subst j; simp
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := equality_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb,Subtype.ext_iff] using he

include e3 e4 in
theorem represented_mem (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : (v i).1 ∈ (v j).1 ↔ (w i).1 ∈ (w j).1 := by
  by_cases hij : i = j
  · subst j
    exact iff_of_false (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
      (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := membership_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb] using he

omit [Fintype I] [DecidableEq V] in
theorem represented_atom (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) : isSet (v i).1 = false ↔ isSet (w i).1 = false := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  rw [←ha i,←hb i]
  cases φ i <;> simp

omit [Fintype I] in
private theorem base_value (φ ψ : Form (Fin s) (Set (Formula R I)))
    (a b : Fin s → A) (r : R) :
    (∃ x y, Form.value S e2 φ a = Hereditary.atom x ∧
      Form.value S e2 ψ b = Hereditary.atom y ∧ S.rel r x y) ↔
    match φ,ψ with
    | .atom i, .atom j => S.rel r (a i) (b j)
    | _, _ => False := by
  have hn (n : ℕ) (child : Fin n → Form (Fin s) (Set (Formula R I)))
      (label : Fin n → Set (Formula R I)) (c : Fin s → A) (x : A) :
      Form.value S e2 (.set n child label) c ≠ Hereditary.atom x := by
    intro h; have hh := congrArg isSet h; simp at hh
  cases φ <;> cases ψ <;> simp [Form.value_atom,atom_injective.eq_iff,hn]

omit [DecidableEq V] in
omit [Fintype I] in
theorem represented_base (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (r : R) (i j : V) :
    (hfStructure S).rel (.base r) (v i) (v j) ↔ (hfStructure T).rel (.base r) (w i) (w j) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  change (∃ x y, (v i).1 = Hereditary.atom x ∧ (v j).1 = Hereditary.atom y ∧ S.rel r x y) ↔
    (∃ x y, (w i).1 = Hereditary.atom x ∧ (w j).1 = Hereditary.atom y ∧ T.rel r x y)
  rw [←ha i,←ha j,←hb i,←hb j,base_value S e2,base_value T e2]
  cases hi : φ i with
  | set n child label => simp
  | atom k =>
    cases hj : φ j with
    | set n child label => simp
    | atom l =>
      have he := (typeOf_eq_iff S T (tupleNames ef) _ _).mp ht
        (.relation r (ef (i,k)) (ef (j,l))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply] using he

omit [Fintype V] in
@[simp] theorem splitBlock_symm_new (i : V) (k : Fin s) :
    (splitBlock (s := s) i).symm (i,k) = .inr k := by simp [splitBlock]

omit [Fintype V] in
@[simp] theorem splitBlock_symm_old (i j : V) (h : j ≠ i) (k : Fin s) :
    (splitBlock (s := s) i).symm (j,k) = .inl (⟨j,h⟩,k) := by simp [splitBlock,h]

omit [Fintype I] [Fintype A] in
private theorem homogeneity_reindex {J K : Type*} [Fintype J] [Fintype K]
    (S : Structure R A) (e : J ↪ I) (f : K ↪ I) (u : K ≃ J)
    (hh : ∀ a b : J → A, tupleType S e a = tupleType S e b →
      ∃ g : G, ∀ j, g • a j = b j) :
    ∀ a b : K → A, tupleType S f a = tupleType S f b → ∃ g : G, ∀ j, g • a j = b j := by
  intro a b hab
  have h := tupleType_project S S f e u.symm.toEmbedding a b hab
  obtain ⟨g,hg⟩ := hh _ _ h
  exact ⟨g,fun j => by simpa using hg (u j)⟩

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include eplus e3 e4 hAutA hAutB in


theorem represented_extension (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, Represented S T ef e2 (Function.update v i x) (Function.update w i (f x)) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  let P := {j : V // j ≠ i} × Fin s
  let u : P ⊕ Fin s ≃ V × Fin s := splitBlock i
  let ep := u.toEmbedding.trans ef
  let epp := (Equiv.sumCongr u (Equiv.refl (Fin s))).toEmbedding.trans eplus
  let e0 := Function.Embedding.inl.trans ep
  let keep : P ↪ V × Fin s := Function.Embedding.inl.trans u.toEmbedding
  let p : P → A := a ∘ keep
  let q : P → B := b ∘ keep
  have hp : tupleType S e0 p = tupleType T e0 q :=
    tupleType_project S T ef e0 keep a b ht
  have homA := homogeneity_reindex S ef ep u hHomA
  have homB := homogeneity_reindex T ef ep u hHomB
  obtain ⟨f,hf⟩ := supported_domain_bijection S T ep epp e2 e3 e4
    hAutA hAutB hs e0 hHomA2 hHomB2 homA homB p q hp
  refine ⟨f,fun x => ?_⟩
  obtain ⟨ψ,c,d,hc,hd,hcd⟩ := hf x
  let a' := Sum.elim p c ∘ u.symm
  let b' := Sum.elim q d ∘ u.symm
  refine ⟨Function.update φ i ψ,a',b',?_,?_,?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [a',u,Function.comp_def,splitBlock] using hc
    · simpa [a',u,p,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using ha j
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [b',u,Function.comp_def,splitBlock] using hd
    · simpa [b',u,q,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using hb j
  · exact tupleType_project S T ep ef u.symm.toEmbedding _ _ hcd

include eplus e3 e4 hAutA hAutB in


theorem supported_eval_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (φ : Formula (HFRelation R) V)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  apply Formula.eval_of_bijectionSystem (hfStructure S) (hfStructure T)
    (Represented S T ef e2) _ _ _ φ v w h
  · exact represented_equal S T ef e2 e3 e4
  · intro v w h r i j
    cases r with
    | mem => exact represented_mem S T ef e2 e3 e4 v w h i j
    | atom => exact represented_atom S T ef e2 v w h i
    | base r => exact represented_base S T ef e2 v w h r i j
  · exact represented_extension S T ef e2 e3 e4 eplus hAutA hAutB hs
      hHomA2 hHomB2 hHomA hHomB

include eplus e3 e4 hAutA hAutB in


theorem supported_sentences_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim)
    (φ : Formula (HFRelation R) V) (hφ : φ.free = ∅)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  let a : V × Fin s → A := fun _ => Classical.choice inferInstance
  have he : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I)
      (a ∘ (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s)) =
        tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim := by
    convert hbase using 1
    congr 1; funext x; exact x.elim
  obtain ⟨b,_,hab⟩ := tupleType_extend S T
    (Function.Embedding.ofIsEmpty : Empty ↪ I) ef
    (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s) a Empty.elim he
  let emptyForm : Form (Fin s) (Set (Formula R I)) := .set 0 Fin.elim0 Fin.elim0
  let v' : V → Domain (A := A) G s := fun i =>
    ⟨Form.value S e2 emptyForm (fun j => a (i,j)),
      value_hereditarily_supported S e2 hAutA emptyForm _⟩
  let w' : V → Domain (A := B) H s := fun i =>
    ⟨Form.value T e2 emptyForm (fun j => b (i,j)),
      value_hereditarily_supported T e2 hAutB emptyForm _⟩
  have hr : Represented S T ef e2 v' w' :=
    ⟨(fun _ => emptyForm),a,b,(fun _ => rfl),(fun _ => rfl),hab⟩
  have hh := supported_eval_transfer S T ef e2 e3 e4 eplus hAutA hAutB hs
    hHomA2 hHomB2 hHomA hHomB φ v' w' hr
  exact (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)).trans
    (hh.trans (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)))

def namesOfCard {J : Type*} [Fintype J] {M : ℕ} (h : Fintype.card J ≤ M) : J ↪ Fin M :=
  (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb h)

def HomogeneousThrough (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (M r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ e : Fin k ↪ Fin M, ∀ a b : Fin k → A,
    tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j

omit [Fintype A] in
private theorem homogeneous_tuple {J : Type*} [Fintype J] {M r : ℕ}
    (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (h : HomogeneousThrough S G M r) (e : J ↪ Fin M)
    (hc : Fintype.card J ≤ r) :
    ∀ a b : J → A, tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j := by
  exact homogeneity_reindex S ((Fintype.equivFin J).symm.toEmbedding.trans e) e
    (Fintype.equivFin J) (h _ hc _)

theorem hf_transfer {m M : ℕ} (hs : 0 < s) (_hm : 0 < m) (hM : 0 < M)
    (hwidth : max 4 (m+1) * s ≤ M)
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : HomogeneousThrough S G M (max 2 m * s))
    (hHomB : HomogeneousThrough T H M (max 2 m * s))
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim)
    (φ : Formula (HFRelation R) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Domain (A := A) G s) (w : Fin m → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  have h4 : 4*s ≤ M := (Nat.mul_le_mul_right s (le_max_left _ _)).trans hwidth
  have hp : (m+1)*s ≤ M := (Nat.mul_le_mul_right s (le_max_right _ _)).trans hwidth
  have h2 : Fintype.card (Fin s ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h3 : Fintype.card ((Fin s ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h4' : Fintype.card (((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have hpf : Fintype.card ((Fin m × Fin s) ⊕ Fin s) ≤ M := by simpa [Nat.add_mul] using hp
  have hfull : Fintype.card (Fin m × Fin s) ≤ M := by simp only [Fintype.card_prod,Fintype.card_fin]; nlinarith
  have hom2 : Fintype.card (Fin s ⊕ Fin s) ≤ max 2 m*s := by
    simpa [two_mul] using Nat.mul_le_mul_right s (le_max_left 2 m)
  have homf : Fintype.card (Fin m × Fin s) ≤ max 2 m*s := by
    simpa using Nat.mul_le_mul_right s (le_max_right 2 m)
  exact supported_sentences_transfer S T (namesOfCard hfull) (namesOfCard h2)
    (namesOfCard h3) (namesOfCard h4') (namesOfCard hpf) hAutA hAutB hs
    (homogeneous_tuple S G hHomA _ hom2) (homogeneous_tuple T H hHomB _ hom2)
    (homogeneous_tuple S G hHomA _ homf) (homogeneous_tuple T H hHomB _ homf)
    hbase φ hφ v w

end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A G : Type*} [Group G] [MulAction G A]

theorem supports_pad {k s : ℕ} (hks : k ≤ s) (a₀ : A) (alpha : Fin k → A)
    {x : HF A} (h : Supports (G := G) alpha x) : Supported (G := G) s x := by
  classical
  let beta (i : Fin s) : A := if hi : i.val < k then alpha ⟨i.val,hi⟩ else a₀
  refine ⟨beta,?_⟩
  intro g hg
  apply h g
  intro i
  have hi := hg (i.castLE hks)
  simpa only [beta, Fin.val_castLE, dite_eq_left i.isLt] using hi

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Grid

open Support Hereditary

noncomputable section

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem central_smul_HF (k : CentralGroup n) (x : HF (Atom b)) :
    k • x = centralHom k • x := rfl

theorem small_orbit_supported (hn : 1 ≤ n) (x : HF (Atom b))
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ)^q) :
    Supported (G := CentralGroup n) ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  classical
  obtain ⟨T,hT,hfix⟩ := small_orbit_support_edges x N hN q hq horbit
  obtain ⟨alpha,ha⟩ := edge_support_tuple (b := b) T x hfix
  have hsupport : Supports (G := CentralGroup n) alpha x := by
    intro k hk
    exact ha k hk
  have hlen : T.card ≤ ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ := by
    exact_mod_cast le_trans hT (Nat.le_ceil _)
  let a₀ : Atom b := zeroEdgeAtom b (ex ⟨0,by omega⟩ 0 0)
  exact supports_pad hlen a₀ alpha hsupport

theorem orbit_card_le_invariant_family (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F) {x : HF (Atom b)} (hx : x ∈ F) :
    Nat.card (MulAction.orbit (BoxGroup n) x) ≤ F.card := by
  classical
  let f : MulAction.orbit (BoxGroup n) x → {y // y ∈ F} := fun y =>
    ⟨y.val,by obtain ⟨g,hg⟩ := y.property; rw [← hg]; exact hF g x hx⟩
  have hf : Function.Injective f := by
    intro a c h
    exact Subtype.ext (congrArg (fun z : {y // y ∈ F} => z.val) h)
  have hn := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hn

theorem invariant_family_hereditarily_supported (hn : 1 ≤ n)
    (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F)
    (htrans : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (hsize : (F.card : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ F, HereditarilySupported (G := CentralGroup n)
      ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  intro x hx y hy
  have hymem : y ∈ F := by
    induction hy with
    | refl => exact hx
    | @tail z w hpath hmem ih => exact ih (htrans w hx z hmem)
  apply small_orbit_supported hn y N hN q hq
  exact le_trans (by exact_mod_cast orbit_card_le_invariant_family F hF hymem) hsize

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem atom_nonempty (hn : 1 ≤ n) (b : Vertex n → Scalar) : Nonempty (Atom b) :=
  ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩

instance atom_nonempty_succ (b : Vertex (n+1) → Scalar) : Nonempty (Atom b) := atom_nonempty (by omega) b

theorem central_analysis_isomorphism (k : CentralGroup n) (r : AnalysisSymbol) (x y : Atom b) :
    (analysisStructure b).rel r (k • x) (k • y) ↔ (analysisStructure b).rel r x y :=
  ((central_atomShift k x).analysisRelation (central_atomShift k y) r).symm

theorem homogeneous_through_numeric (hn : 1 ≤ n) [Nonempty (Atom b)] (R : ℕ)
    (hw : (7*R:ℝ)+7*((6*R:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M) :
    Forms.HomogeneousThrough (analysisStructure b) (CentralGroup n) M R := by
  intro k hk names a a' ht
  apply quantitative_homogeneity hn names a a' _ ht
  simp only [Fintype.card_fin]
  have hkr : (k:ℝ) ≤ R := by exact_mod_cast hk
  have hp : ((6*k:ℝ)/boxConstant)^((3:ℝ)/2) ≤ ((6*R:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) boxConstant_pos.le
  linarith

theorem base_empty_type (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    [Nonempty (Atom (0 : Vertex n → Scalar))] [Nonempty (Atom (Pi.single vstar 1))] :
    Counting.tupleType (analysisStructure (0 : Vertex n → Scalar))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
    Counting.tupleType (analysisStructure (Pi.single vstar 1))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim := by
  apply (Counting.typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  have he : φ.free = ∅ := by
    apply subset_empty.mp
    simpa only [Counting.tupleNames,Finset.univ_eq_empty,Finset.map_empty] using hφ
  exact base_equivalence_numeric hn hbound vstar φ he _ _

theorem grid_hf_transfer (hn : 1 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (vstar : Vertex n) [Nonempty (Atom (0 : Vertex n → Scalar))]
    [Nonempty (Atom (Pi.single vstar 1))]
    (hwidth : max 4 (m+1)*s ≤ M)
    (hhom : (7*(max 2 m*s):ℝ)+7*((6*(max 2 m*s):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    (φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Forms.Domain (A := Atom (0 : Vertex n → Scalar)) (CentralGroup n) s)
    (w : Fin m → Forms.Domain (A := Atom (Pi.single vstar 1)) (CentralGroup n) s) :
    φ.eval (Forms.hfStructure (analysisStructure (0 : Vertex n → Scalar))) v ↔
      φ.eval (Forms.hfStructure (analysisStructure (Pi.single vstar 1))) w := by
  have hM : 0 < M := lt_of_lt_of_le (Nat.mul_pos (by omega) hs) hwidth
  exact Forms.hf_transfer _ _ hs hm hM hwidth
    (fun g r a b => central_analysis_isomorphism g r a b)
    (fun g r a b => central_analysis_isomorphism g r a b)
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (base_empty_type hn hgiant vstar) φ hφ v w

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Interpretations

structure Structure (R : Type) where
  Carrier : Type
  finite : Fintype Carrier
  rel : R → Carrier → Carrier → Bool

attribute [instance] Structure.finite

inductive Formula (R : Type) : ℕ → Type
  | falsum {n} : Formula R n
  | eq {n} (x y : Fin n) : Formula R n
  | rel {n} (r : R) (x y : Fin n) : Formula R n
  | neg {n} : Formula R n → Formula R n
  | and {n} : Formula R n → Formula R n → Formula R n
  | ex {n} : Formula R (n+1) → Formula R n
  | hartig {n} : Formula R (n+1) → Formula R (n+1) → Formula R n

noncomputable def Formula.eval {R : Type} (A : Structure R) :
    {n : ℕ} → Formula R n → (Fin n → A.Carrier) → Prop
  | _, .falsum, _ => False
  | _, .eq x y, v => v x = v y
  | _, .rel r x y, v => A.rel r (v x) (v y) = true
  | _, .neg φ, v => ¬ φ.eval A v
  | _, .and φ ψ, v => φ.eval A v ∧ ψ.eval A v
  | _, .ex φ, v => ∃ a, φ.eval A (Fin.cons a v)
  | _, .hartig φ ψ, v =>
    Nat.card {a : A.Carrier // φ.eval A (Fin.cons a v)} =
    Nat.card {a : A.Carrier // ψ.eval A (Fin.cons a v)}

def Formula.holds {R : Type} (φ : Formula R 0) (A : Structure R) : Prop :=
  φ.eval A Fin.elim0

structure Interpretation (R T : Type) where
  domain : Formula R 2
  identify : Formula R 4
  relation : T → Formula R 4

namespace Interpretation

variable {R T : Type} (I : Interpretation R T) (A : Structure R)

abbrev Domain := {a : A.Carrier × A.Carrier // I.domain.eval A ![a.1,a.2]}

def link (a b : I.Domain A) : Prop :=
  I.identify.eval A ![a.val.1,a.val.2,b.val.1,b.val.2]

def classSetoid : Setoid (I.Domain A) :=
  Relation.EqvGen.setoid (I.link A)

abbrev Vertex := Quotient (I.classSetoid A)

noncomputable def apply : Structure T := by
  classical
  letI : Fintype (I.Domain A) := Fintype.ofFinite _
  letI : Fintype (I.Vertex A) := Fintype.ofFinite _
  exact {
    Carrier := I.Vertex A
    finite := inferInstance
    rel := fun r x y => decide (∃ a b : I.Domain A,
      Quotient.mk (I.classSetoid A) a = x ∧
      Quotient.mk (I.classSetoid A) b = y ∧
      (I.relation r).eval A ![a.val.1,a.val.2,b.val.1,b.val.2]) }

end Interpretation

structure Program (InputSymbols : Type) where
  StateSymbols : Type
  stateFinite : Fintype StateSymbols
  init : Interpretation InputSymbols StateSymbols
  step : Interpretation StateSymbols StateSymbols
  halt : Formula StateSymbols 0
  output : Formula StateSymbols 0

namespace Program

variable {R : Type} (P : Program R)

noncomputable def state (A : Structure R) : ℕ → Structure P.StateSymbols
  | 0 => P.init.apply A
  | j+1 => P.step.apply (state A j)

def haltsAt (A : Structure R) (j : ℕ) : Prop :=
  P.halt.holds (P.state A j) ∧ ∀ k < j, ¬ P.halt.holds (P.state A k)

noncomputable def cost (A : Structure R) (j : ℕ) : ℕ :=
  (j+1) + ∑ k ∈ Finset.range (j+1), Fintype.card (P.state A k).Carrier

def accepts (A : Structure R) : Prop :=
  ∃ j, P.haltsAt A j ∧ P.output.holds (P.state A j)

def polynomiallyBounded : Prop :=
  ∃ c d : ℕ, ∀ A : Structure R, ∃ j,
    P.haltsAt A j ∧ P.cost A j ≤ c * (Fintype.card A.Carrier + 1)^d

def decides (Q : Structure R → Prop) : Prop :=
  P.polynomiallyBounded ∧ ∀ A, P.accepts A ↔ Q A

end Program

def NondefinableByInterpretations {R : Type} (Q : Structure R → Prop) : Prop :=
  ¬ ∃ P : Program R, P.decides Q

end WitnessedSeparation.Interpretations



namespace WitnessedSeparation.Interpretations

noncomputable section

open Classical Finset Hereditary

variable {R T A : Type} (I : Interpretation R T) (S : Structure R)

def payload (e : S.Carrier → HF A) (C : I.Vertex S) : HF A :=
  ofFinset ((univ.filter (fun p : I.Domain S => Quotient.mk (I.classSetoid S) p = C)).image
    (fun p => pair (e p.val.1) (e p.val.2)))

theorem mem_payload (e : S.Carrier → HF A) (C : I.Vertex S) (x : HF A) :
    x ∈ payload I S e C ↔ ∃ p : I.Domain S,
      Quotient.mk (I.classSetoid S) p = C ∧ x = pair (e p.val.1) (e p.val.2) := by
  simp only [payload,mem_ofFinset,mem_image,mem_filter,mem_univ,true_and]
  exact exists_congr (fun p => and_congr_right (fun _ => eq_comm))

theorem payload_injective (e : S.Carrier → HF A) (he : Function.Injective e) :
    Function.Injective (payload I S e) := by
  intro C D h
  obtain ⟨p,rfl⟩ := Quotient.exists_rep C
  have hm : pair (e p.val.1) (e p.val.2) ∈ payload I S e (Quotient.mk _ p) :=
    (mem_payload I S e _ _).mpr ⟨p,rfl,rfl⟩
  rw [h] at hm
  obtain ⟨q,hq,hpq⟩ := (mem_payload I S e D _).mp hm
  have hh := pair_injective hpq
  have heq : p = q := Subtype.ext (Prod.ext (he hh.1) (he hh.2))
  rw [heq]
  exact hq

def vertexCode (e : S.Carrier → HF A) (j : ℕ) (C : I.Vertex S) : HF A :=
  pair (ordinal j) (payload I S e C)

theorem vertexCode_injective (e : S.Carrier → HF A) (he : Function.Injective e) (j : ℕ) :
    Function.Injective (vertexCode I S e j) := by
  intro C D h
  exact payload_injective I S e he (pair_injective h).2

def pairFamily (e : S.Carrier → HF A) : Finset (HF A) :=
  univ.biUnion (fun p : I.Domain S => wrappers (e p.val.1) (e p.val.2))

def classFamily (e : S.Carrier → HF A) (j : ℕ) : Finset (HF A) :=
  univ.biUnion (fun C : I.Vertex S => insert (payload I S e C)
    (wrappers (ordinal j) (payload I S e C)))

theorem pairFamily_card_le (e : S.Carrier → HF A) :
    (pairFamily I S e).card ≤ 3*Fintype.card S.Carrier^2 := by
  calc
    (pairFamily I S e).card ≤ ∑ p : I.Domain S, (wrappers (e p.val.1) (e p.val.2)).card :=
      card_biUnion_le
    _ ≤ ∑ _p : I.Domain S, 3 := sum_le_sum (fun p _ => wrappers_card_le _ _)
    _ = 3*Fintype.card (I.Domain S) := by simp [mul_comm]
    _ ≤ 3*Fintype.card S.Carrier^2 := by
      apply Nat.mul_le_mul_left
      have h := Fintype.card_subtype_le (fun p : S.Carrier × S.Carrier => I.domain.eval S ![p.1,p.2])
      simpa only [Fintype.card_prod,pow_two] using h

theorem classFamily_card_le (e : S.Carrier → HF A) (j : ℕ) :
    (classFamily I S e j).card ≤ 4*Fintype.card (I.Vertex S) := by
  calc
    (classFamily I S e j).card ≤ ∑ C : I.Vertex S,
        (insert (payload I S e C) (wrappers (ordinal j) (payload I S e C))).card := card_biUnion_le
    _ ≤ ∑ _C : I.Vertex S, 4 := by
      apply sum_le_sum
      intro C _
      exact (card_insert_le _ _).trans (by have := wrappers_card_le (ordinal (A := A) j) (payload I S e C); omega)
    _ = 4*Fintype.card (I.Vertex S) := by simp [mul_comm]

theorem stage_family_transitive (e : S.Carrier → HF A) (j : ℕ) (F : Finset (HF A))
    (hF : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (he : ∀ a, e a ∈ F) (hj : ordinal j ∈ F) :
    ∀ x ∈ F ∪ pairFamily I S e ∪ classFamily I S e j,
    ∀ y, y ∈ x → y ∈ F ∪ pairFamily I S e ∪ classFamily I S e j := by
  intro x hx y hy
  have incF : F ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_left _ (mem_union_left _ hz)
  have incP : pairFamily I S e ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_left _ (mem_union_right _ hz)
  have incC : classFamily I S e j ⊆ F ∪ pairFamily I S e ∪ classFamily I S e j :=
    fun z hz => mem_union_right _ hz
  rcases mem_union.mp hx with hx|hx
  · rcases mem_union.mp hx with hx|hx
    · exact incF (hF x hx y hy)
    · obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx
      rcases wrappers_trans hp hy with h|h|h
      · rw [h]; exact incF (he _)
      · rw [h]; exact incF (he _)
      · exact incP (mem_biUnion.mpr ⟨p,mem_univ _,h⟩)
  · obtain ⟨C,_,hC⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hC with rfl|hC
    · obtain ⟨p,hp,hyp⟩ := (mem_payload I S e C y).mp hy
      apply incP
      apply mem_biUnion.mpr
      exact ⟨p,mem_univ _,by simp [hyp,wrappers]⟩
    · rcases wrappers_trans hC hy with h|h|h
      · rw [h]; exact incF hj
      · rw [h]; exact incC (mem_biUnion.mpr ⟨C,mem_univ _,mem_insert_self _ _⟩)
      · exact incC (mem_biUnion.mpr ⟨C,mem_univ _,mem_insert_of_mem h⟩)

end

end WitnessedSeparation.Interpretations



namespace WitnessedSeparation.Counting

noncomputable section

open Classical Finset

variable {R D : Type*} (S : Structure R D) {m n k : ℕ}

def Definable (m n : ℕ) (P : (Fin n → D) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ v, φ.eval S v ↔ P (v ∘ args)

namespace Definable

variable {S} {P Q : (Fin n → D) → Prop}

theorem congr (h : Definable S m n P) (heq : ∀ v, P v ↔ Q v) : Definable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun v => (he v).trans (heq _)⟩

theorem reindex (h : Definable S m n P) (f : Fin n → Fin k) :
    Definable S m k (fun v => P (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun v => he v⟩
  intro i hi
  obtain ⟨j,_,rfl⟩ := mem_image.mp (hφ hi)
  exact mem_image.mpr ⟨f j,mem_univ _,rfl⟩

theorem falsum : Definable S m n (fun _ => False) := by
  intro args
  exact ⟨.falsum,by simp [Formula.free],fun _ => Iff.rfl⟩

theorem neg (h : Definable S m n P) : Definable S m n (fun v => ¬ P v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun v => not_congr (he v)⟩

theorem and (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∧ Q v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun v => and_congr (he v) (he' v)⟩

theorem or (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ∨ Q v) :=
  (h.neg.and h'.neg).neg.congr (fun _ => by tauto)

theorem imp (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v → Q v) :=
  (h.neg.or h').congr (fun _ => by tauto)

theorem iff (h : Definable S m n P) (h' : Definable S m n Q) :
    Definable S m n (fun v => P v ↔ Q v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ => by tauto)

theorem equal (i j : Fin n) : Definable S m n (fun v => v i = v j) := by
  intro args
  refine ⟨.equal (args i) (args j),?_,fun _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩

theorem relation (r : R) (i j : Fin n) : Definable S m n (fun v => S.rel r (v i) (v j)) := by
  intro args
  refine ⟨.relation r (args i) (args j),?_,fun _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩

private theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

private theorem updated_args (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → D) (x : D) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

private theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∃ x, P (Fin.cons x v)) := by
  intro args
  obtain ⟨i,hi⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons i args)
  refine ⟨.ex i φ,free_binder hφ,?_⟩
  intro v
  apply exists_congr
  intro x
  simpa only [updated_args args i hi] using he (Function.update v i x)

theorem all {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) :
    Definable S m n (fun v => ∀ x, P (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ => by simp)

theorem exact {P : (Fin (n+1) → D) → Prop} (h : Definable S m (n+1) P) (hn : n < m) (k : ℕ) :
    Definable S m n (fun v => Nonempty ({x : D // P (Fin.cons x v)} ≃ Fin k)) := by
  intro args
  obtain ⟨i,hi⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons i args)
  refine ⟨.exact i k φ,free_binder hφ,?_⟩
  intro v
  let e : {x : D // φ.eval S (Function.update v i x)} ≃ {x : D // P (Fin.cons x (v ∘ args))} :=
    Equiv.subtypeEquivRight (fun x => by simpa only [updated_args args i hi] using he (Function.update v i x))
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem exists_finset {ι : Type*} {P : ι → (Fin n → D) → Prop} (t : Finset ι)
    (h : ∀ i ∈ t, Definable S m n (P i)) : Definable S m n (fun v => ∃ i ∈ t, P i v) := by
  induction t using Finset.induction_on with
  | empty => exact (falsum (S := S)).congr (fun _ => by simp)
  | @insert i t hi ih =>
    exact ((h i (mem_insert_self _ _)).or (ih (fun j hj => h j (mem_insert_of_mem hj)))).congr
      (fun v => by simp only [mem_insert,exists_eq_or_imp])

theorem bounded_hartig {P Q : (Fin (n+1) → D) → Prop}
    (hP : Definable S m (n+1) P) (hQ : Definable S m (n+1) Q) (hn : n < m) (B : ℕ) :
    Definable S m n (fun v => ∃ k ≤ B,
      Nonempty ({x : D // P (Fin.cons x v)} ≃ Fin k) ∧
      Nonempty ({x : D // Q (Fin.cons x v)} ≃ Fin k)) := by
  apply (exists_finset (range (B+1)) (fun k _ => (hP.exact hn k).and (hQ.exact hn k))).congr
  intro v
  simp only [mem_range,Nat.lt_succ_iff]

end Definable

end

end WitnessedSeparation.Counting

end OAI
