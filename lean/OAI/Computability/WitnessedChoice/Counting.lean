import OAI.Computability.WitnessedChoice.GridAction

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ} {b b' b'' : Vertex n → Scalar}

def shiftLocal (e : Edge n) (z : Scalar) (s : LocalGroup e) : LocalGroup e :=
  Support.H.central (localCycle e) z * s

@[simp] theorem shiftLocal_face (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).face = s.face := by
  simp [shiftLocal,Support.H.mul_face,Support.H.central]

@[simp] theorem shiftLocal_flow (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).flow = z+s.flow := by
  simp [shiftLocal,Support.H.mul_flow,Support.H.central,Support.correction]

@[simp] theorem shiftLocal_zero (e : Edge n) (s : LocalGroup e) : shiftLocal e 0 s = s := by
  ext <;> simp

@[simp] theorem shiftLocal_add (e : Edge n) (z w : Scalar) (s : LocalGroup e) :
    shiftLocal e z (shiftLocal e w s) = shiftLocal e (z+w) s := by
  ext <;> simp [add_assoc]

def localShiftEquiv (e : Edge n) (z : Scalar) : LocalGroup e ≃ LocalGroup e where
  toFun := shiftLocal e z
  invFun := shiftLocal e (-z)
  left_inv := by intro s; simp
  right_inv := by intro s; simp

def shiftStates {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) : LocalStates v :=
  fun e => shiftLocal e.val (t e.val) (s e)

theorem shiftStates_compatible {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v)
    (hs : Compatible s) : Compatible (shiftStates t s) := by
  intro e e' f hf hf'
  simpa only [shiftStates,shiftLocal_face] using hs e e' f hf hf'

theorem shiftStates_divergence {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) :
    divergence (shiftStates t s) = boundary t v + divergence s := by
  simp only [divergence,shiftStates,shiftLocal_flow,mul_add,Finset.sum_add_distrib,sum_incident]

def Configuration.shift {v : Vertex n} (s : Configuration b v) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b' v where
  state := shiftStates t s.state
  compatible := shiftStates_compatible t s.state s.compatible
  charge := by rw [shiftStates_divergence,s.charge,h]; abel

@[simp] theorem Configuration.shift_state {v : Vertex n} (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v - b v) (e : IncidentEdges v) :
    (s.shift t h).state e = shiftLocal e.val (t e.val) (s.state e) := rfl

def configShiftEquiv (v : Vertex n) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b v ≃ Configuration b' v where
  toFun s := s.shift t h
  invFun s := s.shift (-t) (by simp only [map_neg,Pi.neg_apply,h]; abel)
  left_inv s := by apply Configuration.ext; intro e; simp
  right_inv s := by apply Configuration.ext; intro e; simp

inductive AtomShift (t : Edge n → Scalar) : Atom b → Atom b' → Prop
  | edge (e : Edge n) (s : LocalGroup e) :
      AtomShift t (.inl ⟨e,s⟩) (.inl ⟨e,shiftLocal e (t e) s⟩)
  | config (v : Vertex n) (s : Configuration b v) (h : boundary t v = b' v - b v) :
      AtomShift t (.inr ⟨v,s⟩) (.inr ⟨v,s.shift t h⟩)

theorem AtomShift.symm {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : AtomShift (-t) y x := by
  cases h with
  | edge e s => simpa using (AtomShift.edge (b := b') (b' := b) (t := -t) e (shiftLocal e (t e) s))
  | config v s h =>
    have hh : boundary (-t) v = b v - b' v := by simp only [map_neg,Pi.neg_apply,h]; abel
    have he : (s.shift t h).shift (-t) hh = s := by apply Configuration.ext; intro e; simp
    simpa only [he] using (AtomShift.config (t := -t) v (s.shift t h) hh)

theorem AtomShift.functional {t : Edge n → Scalar} {x : Atom b} {y z : Atom b'}
    (hy : AtomShift t x y) (hz : AtomShift t x z) : y = z := by
  cases hy <;> cases hz <;> rfl

theorem AtomShift.equal_iff {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') : x = x' ↔ y = y' := by
  constructor
  · intro he; subst x'; exact h.functional h'
  · intro he; subst y'; exact h.symm.functional h'.symm

theorem AtomShift.relation {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y')
    (hr : AtomRelation b r x x') : AtomRelation b' r y y' := by
  cases hr with
  | ed e s => cases h; cases h'; exact .ed _ _
  | cf v s => cases h; cases h'; exact .cf _ _
  | eb e s a => cases h; cases h'; exact .eb _ _ _
  | vb v s a => cases h; cases h'; exact .vb _ _ _
  | inc v s e => cases h; cases h'; exact .inc _ _ e
  | z e s a δ hz =>
    cases h; cases h'
    apply AtomRelation.z
    simpa only [shiftLocal,mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hz

theorem AtomShift.relation_iff {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y') :
    AtomRelation b r x x' ↔ AtomRelation b' r y y' :=
  ⟨fun hr => h.relation h' hr,fun hr => h.symm.relation h'.symm hr⟩

def blockShiftEquiv (te : Edge n → Edge n → Scalar) (tv : Vertex n → Edge n → Scalar)
    (hv : ∀ v, boundary (tv v) v = b' v - b v) : Atom b ≃ Atom b' :=
  Equiv.sumCongr (Equiv.sigmaCongrRight fun e => localShiftEquiv e (te e e))
    (Equiv.sigmaCongrRight fun v => configShiftEquiv v (tv v) (hv v))

theorem blockShiftEquiv_edge (te : Edge n → Edge n → Scalar) (tv : Vertex n → Edge n → Scalar)
    (hv : ∀ v, boundary (tv v) v = b' v - b v) (e : Edge n) (s : LocalGroup e) :
    blockShiftEquiv te tv hv (.inl ⟨e,s⟩) = .inl ⟨e,shiftLocal e (te e e) s⟩ := rfl

theorem blockShiftEquiv_config (te : Edge n → Edge n → Scalar) (tv : Vertex n → Edge n → Scalar)
    (hv : ∀ v, boundary (tv v) v = b' v - b v) (v : Vertex n) (s : Configuration b v) :
    blockShiftEquiv te tv hv (.inr ⟨v,s⟩) = .inr ⟨v,s.shift (tv v) (hv v)⟩ := rfl

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Counting

noncomputable section

variable {R I A B : Type*}

structure Structure (R : Type*) (A : Type*) where
  rel : R → A → A → Prop

inductive Formula (R I : Type*)
  | falsum
  | equal (x y : I)
  | relation (r : R) (x y : I)
  | neg (φ : Formula R I)
  | and (φ ψ : Formula R I)
  | ex (x : I) (φ : Formula R I)
  | exact (x : I) (n : ℕ) (φ : Formula R I)
  deriving DecidableEq

namespace Formula

variable [DecidableEq I]

def free : Formula R I → Finset I
  | .falsum => ∅
  | .equal x y => {x,y}
  | .relation _ x y => {x,y}
  | .neg φ => φ.free
  | .and φ ψ => φ.free ∪ ψ.free
  | .ex x φ => φ.free.erase x
  | .exact x _ φ => φ.free.erase x

def eval (S : Structure R A) : Formula R I → (I → A) → Prop
  | .falsum, _ => False
  | .equal x y, v => v x = v y
  | .relation r x y, v => S.rel r (v x) (v y)
  | .neg φ, v => ¬ φ.eval S v
  | .and φ ψ, v => φ.eval S v ∧ ψ.eval S v
  | .ex x φ, v => ∃ a, φ.eval S (Function.update v x a)
  | .exact x n φ, v => Nonempty ({a : A // φ.eval S (Function.update v x a)} ≃ Fin n)

theorem eval_congr (S : Structure R A) (φ : Formula R I) {v w : I → A}
    (h : ∀ i ∈ φ.free, v i = w i) : φ.eval S v ↔ φ.eval S w := by
  induction φ generalizing v w with
  | falsum => rfl
  | equal x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | relation r x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | neg φ ih => exact not_congr (ih h)
  | and φ ψ ihφ ihψ =>
    apply and_congr
    · exact ihφ (fun i hi => h i (Finset.mem_union_left _ hi))
    · exact ihψ (fun i hi => h i (Finset.mem_union_right _ hi))
  | ex x φ ih =>
    apply exists_congr
    intro a
    apply ih
    intro i hi
    by_cases heq : i = x
    · subst i; simp
    · simp only [Function.update_of_ne heq]
      exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
  | exact x n φ ih =>
    have heq : ∀ a, φ.eval S (Function.update v x a) ↔ φ.eval S (Function.update w x a) := by
      intro a
      apply ih
      intro i hi
      by_cases heq : i = x
      · subst i; simp
      · simp only [Function.update_of_ne heq]
        exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
    let e := Equiv.subtypeEquivRight heq
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem eval_of_bijectionSystem (S : Structure R A) (T : Structure R B)
    (E : (I → A) → (I → B) → Prop)
    (hequal : ∀ v w, E v w → ∀ i j, (v i = v j ↔ w i = w j))
    (hrel : ∀ v w, E v w → ∀ r i j, S.rel r (v i) (v j) ↔ T.rel r (w i) (w j))
    (hext : ∀ v w, E v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ v w, E v w → (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intro v w h; rfl
  | equal i j => intro v w h; exact hequal v w h i j
  | relation r i j => intro v w h; exact hrel v w h r i j
  | neg φ ih => intro v w h; exact not_congr (ih v w h)
  | and φ ψ ihφ ihψ => intro v w h; exact and_congr (ihφ v w h) (ihψ v w h)
  | ex i φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨e a,(ih _ _ (he a)).mp ha⟩
    · rintro ⟨b,hb⟩
      obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ (he a)).mpr hb⟩
  | exact i n φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ (he a))
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

def conjoin : List (Formula R I) → Formula R I
  | [] => .neg .falsum
  | φ :: l => .and φ (conjoin l)

@[simp] theorem eval_conjoin (S : Structure R A) (l : List (Formula R I)) (v : I → A) :
    (conjoin l).eval S v ↔ ∀ φ ∈ l, φ.eval S v := by
  induction l with
  | nil => simp [conjoin,eval]
  | cons φ l ih => simp [conjoin,eval,ih]

theorem free_conjoin_subset (l : List (Formula R I)) (S : Finset I)
    (h : ∀ φ ∈ l, φ.free ⊆ S) : (conjoin l).free ⊆ S := by
  induction l with
  | nil => simp [conjoin,free]
  | cons φ l ih =>
    exact Finset.union_subset (h φ (by simp)) (ih (fun ψ hψ => h ψ (by simp [hψ])))

end Formula

variable [DecidableEq I]

def typeOf (S : Structure R A) (names : Finset I) (v : I → A) : Set (Formula R I) :=
  {φ | φ.free ⊆ names ∧ φ.eval S v}

theorem typeOf_eq_iff (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) : typeOf S names v = typeOf T names w ↔
      ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) := by
  constructor
  · intro h φ hφ
    have heq := Set.ext_iff.mp h φ
    simpa only [typeOf,Set.mem_ofPred_eq,hφ,true_and] using heq
  · intro h
    ext φ
    exact and_congr_right (h φ)

theorem type_separator (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) (hne : typeOf S names v ≠ typeOf T names w) :
    ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v ∧ ¬ φ.eval T w := by
  classical
  have h : ¬ ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) :=
    fun heq => hne ((typeOf_eq_iff S T names v w).mpr heq)
  push Not at h
  obtain ⟨φ,hφ,hdiff⟩ := h
  by_cases hv : φ.eval S v
  · exact ⟨φ,hφ,hv,by tauto⟩
  · have hw : φ.eval T w := by tauto
    exact ⟨.neg φ,hφ,hv,fun hn => hn hw⟩

theorem isolate_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (v₀ : I → A) :
    ∃ θ : Formula R I, θ.free ⊆ names ∧
      (∀ v, θ.eval S v ↔ typeOf S names v = typeOf S names v₀) ∧
      (∀ w, θ.eval T w ↔ typeOf T names w = typeOf S names v₀) := by
  classical
  let Z := (I → A) ⊕ (I → B)
  let ev : Z → Formula R I → Prop := fun z φ => z.elim (φ.eval S) (φ.eval T)
  let tp : Z → Set (Formula R I) := fun z =>
    z.elim (typeOf S names) (typeOf T names)
  have heq (z : Z) (φ : Formula R I) (hφ : φ.free ⊆ names)
      (h : tp z = typeOf S names v₀) : ev z φ ↔ φ.eval S v₀ := by
    cases z with
    | inl v => exact (typeOf_eq_iff S S names v v₀).mp h φ hφ
    | inr w => exact (typeOf_eq_iff T S names w v₀).mp h φ hφ
  have hcut : ∀ z : Z, ∃ φ : Formula R I,
      φ.free ⊆ names ∧ φ.eval S v₀ ∧ (ev z φ → tp z = typeOf S names v₀) := by
    intro z
    by_cases h : tp z = typeOf S names v₀
    · exact ⟨.neg .falsum,Finset.empty_subset _,not_false,fun _ => h⟩
    · have hs : ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v₀ ∧ ¬ ev z φ := by
        cases z with
        | inl v => exact type_separator S S names v₀ v (Ne.symm h)
        | inr w => exact type_separator S T names v₀ w (Ne.symm h)
      obtain ⟨φ,hφ,hv,hw⟩ := hs
      exact ⟨φ,hφ,hv,fun h' => (hw h').elim⟩
  choose cut hfree htrue hcut using hcut
  let l := (Finset.univ : Finset Z).toList.map cut
  let θ := Formula.conjoin l
  have hf : θ.free ⊆ names := by
    apply Formula.free_conjoin_subset
    intro φ hφ
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hφ
    exact hfree z
  have hall (z : Z) : ev z θ ↔ tp z = typeOf S names v₀ := by
    have hc : ev z θ ↔ ∀ φ ∈ l, ev z φ := by
      cases z with
      | inl v => exact Formula.eval_conjoin S l v
      | inr w => exact Formula.eval_conjoin T l w
    rw [hc]
    constructor
    · intro h
      exact hcut z (h (cut z) (List.mem_map.mpr ⟨z,Finset.mem_toList.mpr (Finset.mem_univ z),rfl⟩))
    · intro h φ hφ
      obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hφ
      exact (heq z (cut z') (hfree z') h).mpr (htrue z')
  exact ⟨θ,hf,fun v => hall (.inl v),fun w => hall (.inr w)⟩

theorem extension_equiv [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (_hi : i ∉ names) (v v₀ : I → A) (w : I → B)
    (htype : typeOf S names v = typeOf T names w) :
    Nonempty ({a : A // typeOf S (insert i names) (Function.update v i a) =
          typeOf S (insert i names) v₀} ≃
        {b : B // typeOf T (insert i names) (Function.update w i b) =
          typeOf S (insert i names) v₀}) := by
  classical
  obtain ⟨θ,hfree,hS,hT⟩ := isolate_type S T (insert i names) v₀
  let X := {a : A // θ.eval S (Function.update v i a)}
  let Y := {b : B // θ.eval T (Function.update w i b)}
  let : Fintype X := Fintype.ofFinite X
  let n := Fintype.card X
  have hf : (Formula.exact i n θ).free ⊆ names := by
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hmem := hfree (Finset.mem_erase.mp hj).2
    exact (Finset.mem_insert.mp hmem).resolve_left hji
  have hn : (Formula.exact i n θ).eval S v := ⟨Fintype.equivFin X⟩
  have hn' := (typeOf_eq_iff S T names v w).mp htype (.exact i n θ) hf |>.mp hn
  obtain ⟨e⟩ := hn'
  let eS := Equiv.subtypeEquivRight (fun a => hS (Function.update v i a))
  let eT := Equiv.subtypeEquivRight (fun b => hT (Function.update w i b))
  exact ⟨eS.symm.trans ((Fintype.equivFin X).trans (e.symm.trans eT))⟩

end





noncomputable section

variable {R I A B : Type*} [DecidableEq I]

namespace Formula

def rename (e : I ≃ I) : Formula R I → Formula R I
  | .falsum => .falsum
  | .equal i j => .equal (e i) (e j)
  | .relation r i j => .relation r (e i) (e j)
  | .neg φ => .neg (φ.rename e)
  | .and φ ψ => .and (φ.rename e) (ψ.rename e)
  | .ex i φ => .ex (e i) (φ.rename e)
  | .exact i n φ => .exact (e i) n (φ.rename e)

@[simp] theorem free_rename (e : I ≃ I) (φ : Formula R I) :
    (φ.rename e).free = φ.free.map e.toEmbedding := by
  induction φ with
  | falsum => simp [rename, free]
  | equal i j => simp [rename, free]
  | relation r i j => simp [rename, free]
  | neg φ ih => simpa [rename, free] using ih
  | and φ ψ ihφ ihψ => simp [rename, free, ihφ, ihψ, Finset.map_union]
  | ex i φ ih => simp [rename, free, ih, Finset.map_erase]
  | exact i n φ ih => simp [rename, free, ih, Finset.map_erase]

@[simp] theorem eval_rename (S : Structure R A) (e : I ≃ I) (φ : Formula R I)
    (v : I → A) : (φ.rename e).eval S v ↔ φ.eval S (v ∘ e) := by
  induction φ generalizing v with
  | falsum => rfl
  | equal i j => rfl
  | relation r i j => rfl
  | neg φ ih => exact not_congr (ih v)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | ex i φ ih =>
    simp only [rename,eval]
    apply exists_congr
    intro a
    rw [ih,Function.update_comp_eq_of_injective _ e.injective]
  | exact i n φ ih =>
    have h (a : A) : (φ.rename e).eval S (Function.update v (e i) a) ↔
        φ.eval S (Function.update (v ∘ e) i a) := by
      rw [ih,Function.update_comp_eq_of_injective _ e.injective]
    let f := Equiv.subtypeEquivRight h
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

end Formula

theorem typeOf_project (S : Structure R A) (T : Structure R B)
    {names small : Finset I} (hsub : small ⊆ names) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S small v = typeOf T small w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact (typeOf_eq_iff _ _ _ _ _).mp h φ (hf.trans hsub)

theorem typeOf_congr (S : Structure R A) (names : Finset I) {v w : I → A}
    (h : ∀ i ∈ names, v i = w i) : typeOf S names v = typeOf S names w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact φ.eval_congr S (fun i hi => h i (hf hi))

theorem typeOf_permute (S : Structure R A) (T : Structure R B)
    (names : Finset I) (e : I ≃ I) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S (names.map e.symm.toEmbedding) (v ∘ e) =
      typeOf T (names.map e.symm.toEmbedding) (w ∘ e) := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  have hf' : (φ.rename e).free ⊆ names := by
    rw [Formula.free_rename]
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨k,hk,hkj⟩ := Finset.mem_map.mp (hf hj)
    simpa only [Equiv.toEmbedding_apply,← hkj,Equiv.apply_symm_apply] using hk
  simpa using (typeOf_eq_iff _ _ _ _ _).mp h (φ.rename e) hf'

theorem extension_bijection [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (hi : i ∉ names) (v : I → A) (w : I → B)
    (h : typeOf S names v = typeOf T names w) :
    ∃ e : A ≃ B, ∀ a, typeOf S (insert i names) (Function.update v i a) =
      typeOf T (insert i names) (Function.update w i (e a)) := by
  classical
  let f : A → Set (Formula R I) := fun a =>
    typeOf S (insert i names) (Function.update v i a)
  let g : B → Set (Formula R I) := fun b =>
    typeOf T (insert i names) (Function.update w i b)
  have he : ∀ ρ, Nonempty ({a // f a = ρ} ≃ {b // g b = ρ}) := by
    intro ρ
    by_cases ha : ∃ a, f a = ρ
    · obtain ⟨a,rfl⟩ := ha
      exact extension_equiv S T names i hi v (Function.update v i a) w h
    · by_cases hb : ∃ b, g b = ρ
      · obtain ⟨b,rfl⟩ := hb
        obtain ⟨e⟩ := extension_equiv T S names i hi w (Function.update w i b) v h.symm
        exact False.elim (ha ⟨(e ⟨b,rfl⟩).1,(e ⟨b,rfl⟩).2⟩)
      · let : IsEmpty {a // f a = ρ} := ⟨fun a => ha ⟨a.1,a.2⟩⟩
        let : IsEmpty {b // g b = ρ} := ⟨fun b => hb ⟨b.1,b.2⟩⟩
        exact ⟨Equiv.equivOfIsEmpty _ _⟩
  let e := Equiv.ofFiberEquiv (fun ρ => Classical.choice (he ρ))
  refine ⟨e,fun a => ?_⟩
  change f a = g (e a)
  exact (Equiv.ofFiberEquiv_map (fun ρ => Classical.choice (he ρ)) a).symm

theorem extend_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names extra : Finset I)
    (v : I → A) (w : I → B) (h : typeOf S names v = typeOf T names w) :
    ∃ w' : I → B, typeOf S (names ∪ extra) v = typeOf T (names ∪ extra) w' ∧
      ∀ i ∈ names, w' i = w i := by
  classical
  induction extra using Finset.induction_on with
  | empty => exact ⟨w,by simpa using h,fun _ _ => rfl⟩
  | @insert i extra hi ih =>
    obtain ⟨w',ht,hw⟩ := ih
    by_cases hin : i ∈ names ∪ extra
    · have heq : names ∪ insert i extra = names ∪ extra := by
        rw [Finset.union_insert,Finset.insert_eq_of_mem hin]
      exact ⟨w',heq ▸ ht,hw⟩
    · obtain ⟨e,he⟩ := extension_bijection S T (names ∪ extra) i hin v w' ht
      refine ⟨Function.update w' i (e (v i)),?_,?_⟩
      · have ht' := he (v i)
        have heq : names ∪ insert i extra = insert i (names ∪ extra) := by
          ext j; simp only [Finset.mem_union,Finset.mem_insert]; tauto
        simpa only [heq,Function.update_eq_self] using ht'
      · intro j hj
        have hji : j ≠ i := by
          intro heq
          apply hin
          rw [←heq]
          exact Finset.mem_union_left extra hj
        rw [Function.update_of_ne hji]
        exact hw j hj

section Tuple

variable {J J' : Type*} [Fintype J] [Fintype J']

def tupleNames (e : J ↪ I) : Finset I := Finset.univ.map e

omit [DecidableEq I] in
@[simp] theorem mem_tupleNames (e : J ↪ I) (i : I) :
    i ∈ tupleNames e ↔ ∃ j, e j = i := by simp [tupleNames]

def tupleAssignment [Nonempty A] (e : J ↪ I) (a : J → A) (i : I) : A :=
  if h : ∃ j, e j = i then a (Classical.choose h) else Classical.choice inferInstance

@[simp] theorem tupleAssignment_apply [Nonempty A] (e : J ↪ I) (a : J → A) (j : J) :
    tupleAssignment e a (e j) = a j := by
  classical
  rw [tupleAssignment,dite_eq_left ⟨j,rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ k, e k = e j from ⟨j,rfl⟩))

def tupleType [Nonempty A] (S : Structure R A) (e : J ↪ I) (a : J → A) :
    Set (Formula R I) := typeOf S (tupleNames e) (tupleAssignment e a)

theorem tupleType_assignment [Nonempty A] (S : Structure R A) (e : J ↪ I)
    (a : J → A) (v : I → A) (h : ∀ j, v (e j) = a j) :
    tupleType S e a = typeOf S (tupleNames e) v := by
  apply typeOf_congr
  intro i hi
  obtain ⟨j,rfl⟩ := (mem_tupleNames e i).mp hi
  rw [tupleAssignment_apply,h]

theorem tupleType_project [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J' ↪ J) (a : J → A) (b : J → B)
    (h : tupleType S e a = tupleType T e b) :
    tupleType S e' (a ∘ u) = tupleType T e' (b ∘ u) := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e' (fun j => e (u j))
    e'.injective (e.injective.comp u.injective)
  have hm : (tupleNames (u.trans e)).map σ.symm.toEmbedding = tupleNames e' := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,by simp only [Function.Embedding.trans_apply,← hσ j,σ.symm_apply_apply]⟩
    · rintro ⟨j,rfl⟩
      refine ⟨e (u j),⟨j,rfl⟩,?_⟩
      rw [← hσ j,σ.symm_apply_apply]
  have hs : tupleNames (u.trans e) ⊆ tupleNames e := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  have hp := typeOf_project S T hs h
  have ht := typeOf_permute S T (tupleNames (u.trans e)) σ hp
  rw [hm] at ht
  rw [tupleType_assignment S e' (a ∘ u) (tupleAssignment e a ∘ σ)
    (fun j => by simp [hσ]),
    tupleType_assignment T e' (b ∘ u) (tupleAssignment e b ∘ σ)
    (fun j => by simp [hσ])]
  exact ht

theorem tupleType_extend [Fintype I] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J ↪ J') (a : J' → A) (b : J → B)
    (h : tupleType S e (a ∘ u) = tupleType T e b) :
    ∃ b' : J' → B, b' ∘ u = b ∧ tupleType S e' a = tupleType T e' b' := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e (fun j => e' (u j))
    e.injective (e'.injective.comp u.injective)
  let v := tupleAssignment e' a
  let w := tupleAssignment e b ∘ σ.symm
  have hw (j : J) : w (e' (u j)) = b j := by
    simp [w,Function.comp_def,←hσ j]
  have hn : (tupleNames e).map σ.toEmbedding = tupleNames (u.trans e') := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,(hσ j).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e j,⟨j,rfl⟩,hσ j⟩
  have ht := typeOf_permute S T (tupleNames e) σ.symm h
  simp only [Equiv.symm_symm,hn] at ht
  have hv : typeOf S (tupleNames (u.trans e')) v =
      typeOf S (tupleNames (u.trans e')) (tupleAssignment e (a ∘ u) ∘ σ.symm) := by
    apply typeOf_congr
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    change tupleAssignment e' a (e' (u j)) =
      tupleAssignment e (a ∘ u) (σ.symm (e' (u j)))
    rw [tupleAssignment_apply,← hσ j,σ.symm_apply_apply,tupleAssignment_apply]
    rfl
  obtain ⟨w',ht',hp⟩ := extend_type S T (tupleNames (u.trans e')) (tupleNames e')
    v w (hv.trans ht)
  have hs : tupleNames (u.trans e') ⊆ tupleNames e' := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  rw [Finset.union_eq_right.mpr hs] at ht'
  refine ⟨fun j => w' (e' j),?_,?_⟩
  · funext j
    rw [Function.comp_apply,hp (e' (u j)) ((mem_tupleNames _ _).mpr ⟨j,rfl⟩),hw]
  · rw [tupleType_assignment T e' _ w' (fun _ => rfl)]
    exact ht'

end Tuple

section Append

variable {J D : Type*} [Fintype J] [Fintype D] [Fintype I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (e' : J ⊕ D ↪ I) (a : J → A) (b : J → B) (c : D → A)
    (h : tupleType S e a = tupleType T e b) :
    ∃ d : D → B, tupleType S e' (Sum.elim a c) = tupleType T e' (Sum.elim b d) := by
  obtain ⟨b',hb',ht⟩ := tupleType_extend S T e e' (Function.Embedding.inl)
    (Sum.elim a c) b h
  refine ⟨b' ∘ Sum.inr,?_⟩
  have heq : b' = Sum.elim b (b' ∘ Sum.inr) := by
    funext j
    cases j with
    | inl j => exact congrFun hb' j
    | inr j => rfl
  rw [heq] at ht
  exact ht

end Append

theorem eval_iso (S : Structure R A) (T : Structure R B) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b))
    (φ : Formula R I) (v : I → A) : φ.eval S v ↔ φ.eval T (e ∘ v) := by
  apply φ.eval_of_bijectionSystem S T (fun v w => ∀ i, w i = e (v i))
  · intro v w h i j
    rw [h i,h j]
    exact e.injective.eq_iff.symm
  · intro v w h r i j
    rw [h i,h j]
    exact he r (v i) (v j)
  · intro v w h i
    refine ⟨e,fun a j => ?_⟩
    by_cases hij : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hij,h j]
  · intro i; rfl

theorem tupleType_iso {J : Type*} [Fintype J] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (names : J ↪ I) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b)) (a : J → A) :
    tupleType S names a = tupleType T names (e ∘ a) := by
  rw [tupleType_assignment T names (e ∘ a) (e ∘ tupleAssignment names a)
    (fun j => by simp)]
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  exact eval_iso S T e he φ _

end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

abbrev ClassLabel (n : ℕ) :=
  (Σ e : Edge n, EdgeFaces e → Support.Plane) ⊕
  (Σ v : Vertex n, (e : IncidentEdges v) → EdgeFaces e.val → Support.Plane)

instance : Fintype (ClassLabel n) := by
  letI : ∀ v : Vertex n, Finite ((e : IncidentEdges v) → EdgeFaces e.val → Support.Plane) :=
    fun v => inferInstance
  exact Fintype.ofFinite _

def classLabel : Atom b → ClassLabel n
  | .inl ⟨e,s⟩ => .inl ⟨e,s.face⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,fun e => (s.state e).face⟩

def classIndex (x : Atom b) : Fin (Fintype.card (ClassLabel n)) :=
  Fintype.equivFin (ClassLabel n) (classLabel x)

inductive AnalysisSymbol
  | input (s : Symbol)
  | preorder
  | raw (δ : Scalar)
  deriving DecidableEq, Fintype

def rawDifference (b : Vertex n → Scalar) (δ : Scalar) : Atom b → Atom b → Prop
  | .inl ⟨e,s⟩, .inl ⟨f,t⟩ => e = f ∧ t.flow - s.flow = δ
  | _, _ => False

def analysisStructure (b : Vertex n → Scalar) : Counting.Structure AnalysisSymbol (Atom b) where
  rel r x y := match r with
    | .input s => AtomRelation b s x y
    | .preorder => classIndex x ≤ classIndex y
    | .raw δ => rawDifference b δ x y

@[simp] theorem classLabel_shiftLocal (e : Edge n) (s : LocalGroup e) (t : Scalar) :
    classLabel (b := b') (.inl ⟨e,shiftLocal e t s⟩) = classLabel (b := b) (.inl ⟨e,s⟩) := by
  simp [classLabel]

@[simp] theorem classLabel_shiftConfig (v : Vertex n) (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v-b v) :
    classLabel (.inr ⟨v,s.shift t h⟩) = classLabel (.inr ⟨v,s⟩) := by
  simp [classLabel]

theorem AtomShift.classLabel {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : Grid.classLabel x = Grid.classLabel y := by
  cases h <;> simp [Grid.classLabel]

theorem AtomShift.analysisRelation {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') (r : AnalysisSymbol) :
    (analysisStructure b).rel r x x' ↔ (analysisStructure b').rel r y y' := by
  cases r with
  | input r => exact h.relation_iff h'
  | preorder => change classIndex x ≤ classIndex x' ↔ classIndex y ≤ classIndex y'
                simp only [classIndex,h.classLabel,h'.classLabel]
  | raw d =>
    change rawDifference b d x x' ↔ rawDifference b' d y y'
    cases h <;> cases h' <;> simp only [rawDifference,shiftLocal_flow]
    rename_i e s f a
    constructor
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩

def predecessors (x : Atom b) : Finset (Atom b) := univ.filter fun y => classIndex y < classIndex x

theorem predecessors_recovers_class {x y : Atom b}
    (h : (predecessors x).card = (predecessors y).card) : classLabel x = classLabel y := by
  have hlt {x y : Atom b} (hxy : classIndex x < classIndex y) :
      (predecessors x).card < (predecessors y).card := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro z hz; exact mem_filter.mpr ⟨mem_univ _,lt_trans (mem_filter.mp hz).2 hxy⟩
    · intro he
      have hx : x ∈ predecessors y := mem_filter.mpr ⟨mem_univ _,hxy⟩
      rw [←he] at hx
      exact (lt_irrefl _) (mem_filter.mp hx).2
  have hi : classIndex x = classIndex y := by
    rcases lt_trichotomy (classIndex x) (classIndex y) with hh | hh | hh
    · exact False.elim ((ne_of_lt (hlt hh)) h)
    · exact hh
    · exact False.elim ((ne_of_lt (hlt hh)) h.symm)
  exact (Fintype.equivFin (ClassLabel n)).injective hi

def classFormula {I : Type*} (x y : I) (h : ℕ) : Counting.Formula AnalysisSymbol I :=
  .exact y h (.and (.relation .preorder y x) (.neg (.relation .preorder x y)))

theorem free_classFormula {I : Type*} [DecidableEq I] (i j : I) (h : ℕ) :
    (classFormula i j h).free ⊆ {i} := by
  simp only [classFormula,Counting.Formula.free]
  intro k hk
  simp only [mem_erase,mem_union,mem_insert,mem_singleton] at hk ⊢
  tauto

theorem eval_classFormula {I : Type*} [DecidableEq I] (v : I → Atom b) {i j : I}
    (hne : i ≠ j) (h : ℕ) :
    (classFormula i j h).eval (analysisStructure b) v ↔ (predecessors (v i)).card = h := by
  have hh (x : Atom b) :
      ((analysisStructure b).rel .preorder (Function.update v j x j) (Function.update v j x i) ∧
      ¬(analysisStructure b).rel .preorder (Function.update v j x i) (Function.update v j x j)) ↔
      x ∈ predecessors (v i) := by
    simp only [analysisStructure,Function.update_self,Function.update_of_ne hne,
      predecessors,mem_filter,mem_univ,true_and,lt_iff_le_not_ge]
  change Nonempty (_ ≃ Fin h) ↔ _
  let e := Equiv.subtypeEquivRight hh
  constructor
  · rintro ⟨f⟩
    simpa using Fintype.card_congr (e.symm.trans f)
  · intro he
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using he)))⟩

theorem type_recovers_classes {I : Type*} [DecidableEq I] (names : Finset I)
    {v w : I → Atom b} (ht : Counting.typeOf (analysisStructure b) names v =
      Counting.typeOf (analysisStructure b) names w) {i j : I} (hi : i ∈ names) (hne : i ≠ j) :
    classLabel (v i) = classLabel (w i) := by
  apply predecessors_recovers_class
  let h := (predecessors (v i)).card
  have hf : (classFormula i j h).free ⊆ names :=
    (free_classFormula i j h).trans (singleton_subset_iff.mpr hi)
  have he := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht (classFormula i j h) hf
  exact ((eval_classFormula w hne h).mp (he.mp ((eval_classFormula v hne h).mpr rfl))).symm

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

abbrev Block (n : ℕ) := Edge n ⊕ Vertex n

def atomBlock : Atom b → Block n
  | .inl ⟨e,_⟩ => .inl e
  | .inr ⟨v,_⟩ => .inr v

def blockEdges : Block n → Finset (Edge n)
  | .inl e => {e}
  | .inr v => univ.filter (incident v)

def touch (x : Atom b) : Finset (Edge n) := blockEdges (atomBlock x)

theorem blockEdges_card (J : Block n) : (blockEdges J).card ≤ 6 := by
  cases J with
  | inl e => simp [blockEdges]
  | inr v =>
    have hh : (blockEdges (.inr v)).card = Fintype.card {e : Edge n // head e = v ∨ tail e = v} := by
      rw [←Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => by simp [blockEdges,incident]))
    rw [hh]
    exact degree_le_six v

theorem touch_card (x : Atom b) : (touch x).card ≤ 6 := blockEdges_card (atomBlock x)

theorem touch_shift {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : touch x = touch y := by cases h <;> rfl

theorem AtomShift.congr {t t' : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) (he : ∀ e ∈ touch x, t e = t' e) : AtomShift t' x y := by
  cases h with
  | edge e s =>
    have hh := he e (by simp [touch,atomBlock,blockEdges])
    simpa only [hh] using (AtomShift.edge (b := b) (b' := b') (t := t') e s)
  | config v s h =>
    have hv : boundary t' v = b' v-b v := by
      rw [←sum_incident,←h,←sum_incident]
      apply sum_congr rfl
      intro e _
      rw [he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    have hs : s.shift t h = s.shift t' hv := by
      apply Configuration.ext
      intro e
      simp only [Configuration.shift_state,he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    rw [hs]
    exact .config v s hv

def touches {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) : Finset (Edge n) :=
  names.biUnion (fun i => touch (v i))

theorem touches_card {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) :
    (touches names v).card ≤ 6*names.card := by
  calc
    _ ≤ ∑ i ∈ names, (touch (v i)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ names, 6 := sum_le_sum (fun i _ => touch_card (v i))
    _ = 6*names.card := by simp [Nat.mul_comm]

theorem touch_subset_touches {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) {i : I} (hi : i ∈ names) : touch (v i) ⊆ touches names v := by
  intro e he; exact mem_biUnion.mpr ⟨i,hi,he⟩

theorem touches_mono {I : Type*} [DecidableEq I] {s t : Finset I} (hst : s ⊆ t)
    (v : I → Atom b) : touches s v ⊆ touches t v := by
  intro e he
  obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨i,hst hi,he⟩

theorem touches_insert_update {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) (i : I) (a : Atom b) :
    touches (insert i (names.erase i)) (Function.update v i a) =
      touches (names.erase i) v ∪ touch a := by
  ext e
  simp only [touches,mem_biUnion,mem_insert,mem_erase,mem_union]
  constructor
  · rintro ⟨j,(rfl | hj),he⟩
    · exact Or.inr (by simpa using he)
    · exact Or.inl ⟨j,hj,by simpa [Function.update_of_ne hj.1] using he⟩
  · rintro (⟨j,hj,he⟩ | he)
    · exact ⟨j,Or.inr hj,by simpa [Function.update_of_ne hj.1] using he⟩
    · exact ⟨i,Or.inl rfl,by simpa using he⟩

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

def HasState (x : Atom b) (e : Edge n) (s : LocalGroup e) : Prop :=
  x = .inl ⟨e,s⟩ ∨ AtomRelation b .I x (.inl ⟨e,s⟩)

@[simp] theorem hasState_edge (f : Edge n) (s : LocalGroup f) (e : Edge n) (t : LocalGroup e) :
    HasState (b := b) (.inl ⟨f,s⟩) e t ↔ (⟨f,s⟩ : Σ e, LocalGroup e) = ⟨e,t⟩ := by
  constructor
  · rintro (h | h)
    · exact Sum.inl.inj h
    · cases h
  · exact fun h => Or.inl (congrArg Sum.inl h)

@[simp] theorem hasState_config (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (t : LocalGroup e) :
    HasState (.inr ⟨v,s⟩) e t ↔ ∃ h : incident v e, s.state ⟨e,h⟩ = t := by
  constructor
  · rintro (h | h)
    · cases h
    · cases h with
      | inc v s e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact Or.inr (.inc v s ⟨e,h⟩)

def stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) : LocalGroup e := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    exact s
  | inr x =>
    rcases x with ⟨v,s⟩
    exact s.state ⟨e,by simpa [touch,atomBlock,blockEdges] using he⟩

@[simp] theorem stateAt_edge (e : Edge n) (s : LocalGroup e)
    (he : e ∈ touch (b := b) (.inl ⟨e,s⟩)) : stateAt (.inl ⟨e,s⟩) e he = s := by
  simp [stateAt]

@[simp] theorem stateAt_config (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v)
    (he : e.val ∈ touch (.inr ⟨v,s⟩)) : stateAt (.inr ⟨v,s⟩) e.val he = s.state e := rfl

theorem hasState_stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) :
    HasState x e (stateAt x e he) := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    simp
  | inr x =>
    rcases x with ⟨v,s⟩
    exact (hasState_config _ _ _ _).mpr ⟨by simpa [touch,atomBlock,blockEdges] using he,rfl⟩

theorem classLabel_edge_iff (y : Atom b) (e : Edge n) (u : EdgeFaces e → Support.Plane) :
    classLabel y = .inl ⟨e,u⟩ ↔ ∃ t : LocalGroup e, y = .inl ⟨e,t⟩ ∧ t.face = u := by
  cases y with
  | inl y =>
    rcases y with ⟨f,s⟩
    constructor
    · intro h
      have hh := Sum.inl.inj h
      have hf := congrArg Sigma.fst hh
      dsimp at hf
      subst f
      have hu := (Sigma.mk.inj_iff.mp hh).2
      exact ⟨s,rfl,eq_of_heq hu⟩
    · rintro ⟨t,h,rfl⟩; cases h; rfl
  | inr y => simp [classLabel]

theorem atomShift_of_states (x y : Atom b) (t : Edge n → Scalar)
    (hc : classLabel x = classLabel y)
    (hs : ∀ e (he : e ∈ touch x), HasState y e (shiftLocal e (t e) (stateAt x e he))) :
    AtomShift t x y := by
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    obtain ⟨s',rfl,hface⟩ := (classLabel_edge_iff y e s.face).mp hc.symm
    have h := hs e (by simp [touch,atomBlock,blockEdges])
    simp only [hasState_edge] at h
    have hh : s' = shiftLocal e (t e) s := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst s'
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    cases y with
    | inl y => cases hc
    | inr y =>
      rcases y with ⟨w,s'⟩
      have hw := congrArg Sigma.fst (Sum.inr.inj hc)
      dsimp at hw
      subst w
      have hstates : s'.state = shiftStates t s.state := by
        funext e
        have he : e.val ∈ touch (.inr ⟨v,s⟩) := by simpa [touch,atomBlock,blockEdges] using e.property
        obtain ⟨h,hval⟩ := (hasState_config _ _ _ _).mp (hs e.val he)
        exact hval
      have hb : boundary t v = b v-b v := by
        have h := s'.charge
        rw [hstates,shiftStates_divergence,s.charge] at h
        linear_combination h
      have hy : s' = s.shift t hb := by
        apply Configuration.ext
        intro e
        exact congrFun hstates e
      rw [hy]
      exact .config v s hb

abbrev Occurrences {J : Type*} (a : J → Atom b) := Σ j : J, {e : Edge n // e ∈ touch (a j)}

def occurrenceAtom {J : Type*} (a : J → Atom b) (o : Occurrences a) : Atom b :=
  .inl ⟨o.2.val,stateAt (a o.1) o.2.val o.2.property⟩

def Augment {J : Type*} (a : J → Atom b) : J ⊕ Occurrences a → Atom b :=
  Sum.elim a (occurrenceAtom a)

structure SameDiagram {J : Type*} (a a' : J → Atom b) : Prop where
  classes : ∀ j, classLabel (a j) = classLabel (a' j)
  equal : ∀ i j, a i = a j ↔ a' i = a' j
  relation : ∀ r i j, (analysisStructure b).rel r (a i) (a j) ↔
    (analysisStructure b).rel r (a' i) (a' j)

theorem augmented_diagram_shift {J : Type*} (a a' : J → Atom b)
    (y : Occurrences a → Atom b) (h : SameDiagram (Augment a) (Sum.elim a' y)) :
    ∃ t : Edge n → Scalar, ∀ j, AtomShift t (a j) (a' j) := by
  have hy (o : Occurrences a) : ∃ s : LocalGroup o.2.val,
      y o = .inl ⟨o.2.val,s⟩ ∧ s.face = (stateAt (a o.1) o.2.val o.2.property).face :=
    (classLabel_edge_iff _ _ _).mp (h.classes (.inr o)).symm
  choose target htarget hface using hy
  let delta (o : Occurrences a) : Scalar :=
    (target o).flow-(stateAt (a o.1) o.2.val o.2.property).flow
  have hd (o p : Occurrences a) (he : o.2.val = p.2.val) : delta o = delta p := by
    have hh := (h.relation (.raw
      ((stateAt (a p.1) p.2.val p.2.property).flow -
        (stateAt (a o.1) o.2.val o.2.property).flow)) (.inr o) (.inr p)).mp
      (show (analysisStructure b).rel _ (Augment a (.inr o)) (Augment a (.inr p)) from ⟨he,rfl⟩)
    change rawDifference b _ (y o) (y p) at hh
    rw [htarget o,htarget p] at hh
    have hh' := hh.2
    dsimp [delta]
    linear_combination -hh'
  let t (e : Edge n) : Scalar := if he : ∃ o : Occurrences a, o.2.val = e
    then delta he.choose else 0
  have ht (o : Occurrences a) : t o.2.val = delta o := by
    have he : ∃ p : Occurrences a, p.2.val = o.2.val := ⟨o,rfl⟩
    simp only [t,dite_eq_left he]
    exact hd he.choose o he.choose_spec
  have heq (o : Occurrences a) :
      target o = shiftLocal o.2.val (t o.2.val) (stateAt (a o.1) o.2.val o.2.property) := by
    apply Support.H.ext
    · simpa only [shiftLocal_face] using hface o
    · simp only [shiftLocal_flow,ht,delta]; abel
  refine ⟨t,fun j => atomShift_of_states _ _ _ (h.classes (.inl j)) ?_⟩
  intro e he
  let o : Occurrences a := ⟨j,e,he⟩
  have hs := hasState_stateAt (a j) e he
  have hh : a' j = y o ∨ AtomRelation b .I (a' j) (y o) :=
    hs.elim (fun hh => Or.inl ((h.equal (.inl j) (.inr o)).mp hh))
      (fun hh => Or.inr ((h.relation (.input .I) (.inl j) (.inr o)).mp hh))
  rw [htarget o,heq o] at hh
  exact hh

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I] [Nonempty (Atom b)]

omit [Fintype I] in
theorem sameDiagram_of_type (names : J ↪ I) (a a' : J → Atom b)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a')
    (spare : I) (hsp : spare ∉ Counting.tupleNames names) : SameDiagram a a' := by
  have hmem (j : J) : names j ∈ Counting.tupleNames names := by simp
  refine ⟨?_,?_,?_⟩
  · intro j
    have hn : names j ≠ spare := by intro h; exact hsp (h ▸ hmem j)
    have hh := type_recovers_classes (Counting.tupleNames names) ht (hmem j) hn
    simpa only [Counting.tupleAssignment_apply] using hh
  · intro i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.equal (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh
  · intro r i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.relation r (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh

end

end WitnessedSeparation.Grid

end OAI
