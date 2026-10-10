import OAI.ModelTheory.Choiceless.Bounds

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF

@[simp] theorem truth_ne_empty : (truth : HF A) ≠ empty :=
  fun h => by have := ordinal_injective h; omega

@[simp] theorem boolean_truth (p : Prop) : boolean (A := A) p = truth ↔ p := by
  by_cases h : p <;> simp [boolean,h,Ne.symm truth_ne_empty]

lemma uniqueHF_spec (x : HF A) :
    (∃ a, elements x = {a} ∧ uniqueHF x = a) ∨
      (¬ ∃ a, elements x = {a}) ∧ uniqueHF x = empty := by
  by_cases h : ∃ a, elements x = {a}
  · exact Or.inl ⟨h.choose,h.choose_spec,by simp only [uniqueHF,dite_eq_left h]⟩
  · exact Or.inr ⟨h,by simp only [uniqueHF,dite_eq_right h]⟩

inductive Term (R F : Type*) (arity : F → ℕ) : ℕ → Type _
  | var {k} (i : Fin k) : Term R F arity k
  | constant {k} (n : ℕ) : Term R F arity k
  | atoms {k} : Term R F arity k
  | app {k} (f : F) (args : Fin (arity f) → Term R F arity k) : Term R F arity k
  | pair {k} (a b : Term R F arity k) : Term R F arity k
  | union {k} (a : Term R F arity k) : Term R F arity k
  | unique {k} (a : Term R F arity k) : Term R F arity k
  | card {k} (a : Term R F arity k) : Term R F arity k
  | equal {k} (a b : Term R F arity k) : Term R F arity k
  | member {k} (a b : Term R F arity k) : Term R F arity k
  | isAtom {k} (a : Term R F arity k) : Term R F arity k
  | input {k} (r : R) (a b : Term R F arity k) : Term R F arity k
  | not {k} (a : Term R F arity k) : Term R F arity k
  | and {k} (a b : Term R F arity k) : Term R F arity k
  | conditional {k} (c a b : Term R F arity k) : Term R F arity k
  | comprehension {k} (bound : Term R F arity k)
      (guard body : Term R F arity (k+1)) : Term R F arity k

abbrev Valuation := Location F arity A → HF A

namespace State

@[simp] theorem mem_support (s : State F arity A) (l : Location F arity A) :
    l ∈ s.support ↔ s.value l ≠ empty := Set.Finite.mem_toFinset _

end State

namespace Term

variable [Fintype A]

def eval (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → (Fin k → HF A) → HF A
  | _, .var i, v => v i
  | _, .constant n, _ => ordinal n
  | _, .atoms, _ => allAtoms
  | _, .app f args, v => s.value ⟨f,fun i => eval rel s (args i) v⟩
  | _, .pair a b, v => double (eval rel s a v) (eval rel s b v)
  | _, .union a, v => unionHF (eval rel s a v)
  | _, .unique a, v => uniqueHF (eval rel s a v)
  | _, .card a, v => cardinalityHF (eval rel s a v)
  | _, .equal a b, v => boolean (eval rel s a v = eval rel s b v)
  | _, .member a b, v => boolean (eval rel s a v ∈ eval rel s b v)
  | _, .isAtom a, v => boolean (isSet (eval rel s a v) = false)
  | _, .input r a b,v => boolean (inputRelation rel r (eval rel s a v) (eval rel s b v))
  | _, .not a,v => boolean (eval rel s a v ≠ truth)
  | _, .and a b,v => boolean (eval rel s a v = truth ∧ eval rel s b v = truth)
  | _, .conditional c a b,v => if eval rel s c v = truth then eval rel s a v else eval rel s b v
  | _, .comprehension bound guard body,v =>
      ofFinset (((elements (eval rel s bound v)).filter
        (fun x => eval rel s guard (Fin.cons x v) = truth)).image
        (fun x => eval rel s body (Fin.cons x v)))

end Term

inductive Rule (R F : Type*) (arity : F → ℕ) : ℕ → Type _
  | skip {k} : Rule R F arity k
  | update {k} (f : F) (args : Fin (arity f) → Term R F arity k)
      (value : Term R F arity k) : Rule R F arity k
  | parallel {k} (a b : Rule R F arity k) : Rule R F arity k
  | conditional {k} (c : Term R F arity k) (a b : Rule R F arity k) : Rule R F arity k
  | forall {k} (bound : Term R F arity k) (body : Rule R F arity (k+1)) : Rule R F arity k
  | letValue {k} (value : Term R F arity k) (body : Rule R F arity (k+1)) : Rule R F arity k

namespace Rule

variable [Fintype A]

def updates (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Rule R F arity k → (Fin k → HF A) → Finset (Update F arity A)
  | _, .skip, _ => ∅
  | _, .update f args value, v => { (⟨f,fun i => (args i).eval rel s v⟩,value.eval rel s v) }
  | _, .parallel a b,v => updates rel s a v ∪ updates rel s b v
  | _, .conditional c a b,v => if c.eval rel s v = truth then updates rel s a v else updates rel s b v
  | _, .forall bound body,v => (elements (bound.eval rel s v)).biUnion
      (fun x => updates rel s body (Fin.cons x v))
  | _, .letValue value body,v => updates rel s body (Fin.cons (value.eval rel s v) v)

end Rule

namespace State

lemma updatedValue_eq (s : State F arity A) (u : Finset (Update F arity A))
    (hu : Consistent u) {l : Location F arity A} {x : HF A} (hx : (l,x) ∈ u) :
    s.updatedValue u l = x := by
  have h : ∃ y, (l,y) ∈ u := ⟨x,hx⟩
  simp only [updatedValue,dite_eq_left h]
  exact hu l _ _ h.choose_spec hx

lemma updatedValue_default (s : State F arity A) (u : Finset (Update F arity A))
    {l : Location F arity A} (hl : ¬ ∃ x, (l,x) ∈ u) : s.updatedValue u l = s.value l := by
  simp only [updatedValue,dite_eq_right hl]

end State

instance : Fintype Control where
  elems := {.halt,.accept}
  complete := by intro x; cases x <;> simp

structure Machine (R : Type*) where
  Functions : Type
  finiteFunctions : Fintype Functions
  arity : Functions → ℕ
  rule : Rule R (Control ⊕ Functions) (Sum.elim (fun _ => 0) arity) 0

namespace Machine

variable (P : Machine R) [Fintype A]

abbrev functionArity : Control ⊕ P.Functions → ℕ := Sum.elim (fun _ => 0) P.arity

abbrev Store := State (Control ⊕ P.Functions) P.functionArity A

def flag (s : P.Store (A := A)) (c : Control) : Prop := s.value ⟨.inl c,Fin.elim0⟩ = truth

def step (rel : R → A → A → Bool) (s : P.Store (A := A)) : Option (P.Store (A := A)) :=
  if P.flag s .halt then some s else
    let u := P.rule.updates rel s Fin.elim0
    if State.Consistent u then some (s.applyUpdates u) else none

def run (rel : R → A → A → Bool) : ℕ → Option (P.Store (A := A))
  | 0 => some State.initial
  | j+1 => (run rel j).bind (P.step rel)

def accepts (rel : R → A → A → Bool) : Prop :=
  ∃ h s, P.run rel h = some s ∧ P.flag s .halt ∧ P.flag s .accept

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF_1

@[simp] lemma mem_closure_self (x : HF A) : x ∈ closure x := by rw [closure]; simp

lemma closure_member_subset {x y : HF A} (h : y ∈ x) : closure y ⊆ closure x := by
  nth_rw 2 [closure]
  intro z hz
  simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  exact Or.inr ⟨y,h,hz⟩

lemma mem_closure_iff (x y : HF A) : x ∈ closure y ↔
    Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y := by
  constructor
  · intro h
    induction y using (measure rank).wf.induction with
    | h y ih =>
      rw [closure] at h
      rcases mem_insert.mp h with rfl | hm
      · exact .refl
      · obtain ⟨z,hz,hxz⟩ := mem_biUnion.mp hm
        exact (ih z.val (rank_lt_of_mem z.property) hxz).tail z.property
  · intro h
    induction h with
    | refl => exact mem_closure_self _
    | tail hab hbc ih => exact closure_member_subset hbc ih

lemma closure_transitive {x y z : HF A} (hxy : y ∈ closure x) (hyz : z ∈ y) :
    z ∈ closure x := by
  apply (mem_closure_iff z x).mpr
  exact (Relation.ReflTransGen.single (r := fun a b : HF A => a ∈ b) hyz).trans ((mem_closure_iff y x).mp hxy)

lemma mem_mapEquiv (e : A ≃ B) (x y : HF A) : map e x ∈ map e y ↔ x ∈ y := by
  change map e x ∈ elements (map e y) ↔ x ∈ elements y
  rw [elements_map]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    exact (mapEquiv e).injective he ▸ hz
  · intro h
    exact Finset.mem_image.mpr ⟨x,h,rfl⟩

lemma rtc_map (e : A ≃ B) {x y : HF A}
    (h : Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y) :
    Relation.ReflTransGen (fun a b : HF B => a ∈ b) (map e x) (map e y) := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ((mem_mapEquiv e _ _).mpr hbc)

lemma closure_map (e : A ≃ B) (x : HF A) : closure (map e x) = (closure x).image (map e) := by
  ext y
  obtain ⟨z,rfl⟩ := (mapEquiv e).surjective y
  rw [mem_closure_iff,mem_image]
  constructor
  · intro h
    have h' : Relation.ReflTransGen (fun a b : HF A => a ∈ b) z x := by
      have hm := rtc_map e.symm h
      change Relation.ReflTransGen (fun a b : HF A => a ∈ b)
        ((mapEquiv e).symm ((mapEquiv e) z)) ((mapEquiv e).symm ((mapEquiv e) x)) at hm
      simpa only [Equiv.symm_apply_apply] using hm
    exact ⟨z,(mem_closure_iff z x).mpr h',rfl⟩
  · rintro ⟨w,hw,he⟩
    have h := (mem_closure_iff w x).mp hw
    have hm := rtc_map e h
    exact he ▸ hm

lemma mem_familyClosure {f : Finset (HF A)} {x : HF A} :
    x ∈ familyClosure f ↔ ∃ y ∈ f, x ∈ closure y := by simp [familyClosure]

lemma familyClosure_contains {f : Finset (HF A)} {x : HF A} (hx : x ∈ f) :
    x ∈ familyClosure f := mem_familyClosure.mpr ⟨x,hx,mem_closure_self x⟩

lemma familyClosure_transitive {f : Finset (HF A)} {x y : HF A}
    (hx : x ∈ familyClosure f) (hy : y ∈ x) : y ∈ familyClosure f := by
  obtain ⟨z,hz,hxz⟩ := mem_familyClosure.mp hx
  exact mem_familyClosure.mpr ⟨z,hz,closure_transitive hxz hy⟩

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

attribute [local instance] CPTSeparation.Operational.instDecidableEqHF_1

namespace State

lemma value_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) : s.value l ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_self _ _⟩

lemma argument_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) (i : Fin (arity l.1)) : l.2 i ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,rfl⟩)⟩

lemma active_transitive [Fintype A] (s : State F arity A) {x y : HF A}
    (hx : x ∈ s.active) (hy : y ∈ x) : y ∈ s.active :=
  familyClosure_transitive hx hy

end State

namespace Machine

variable (P : Machine R) [Fintype A]

def runActive (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  (range (h+1)).biUnion fun j => match P.run rel j with
    | none => ∅
    | some s => s.active

lemma state_active_subset (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.runActive rel h := by
  intro x hx
  exact mem_biUnion.mpr ⟨j,by simpa using hj,by simpa only [hs] using hx⟩

lemma runActive_transitive (rel : R → A → A → Bool) (h : ℕ) {x y : HF A}
    (hx : x ∈ P.runActive rel h) (hy : y ∈ x) : y ∈ P.runActive rel h := by
  obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
  cases hs : P.run rel j with
  | none => simp only [hs,Finset.notMem_empty] at hx
  | some s =>
    simp only [hs] at hx
    exact mem_biUnion.mpr ⟨j,hj,by simpa only [hs] using s.active_transitive hx hy⟩

lemma runActive_card_le (rel : R → A → A → Bool) (h K : ℕ)
    (hb : ∀ j ≤ h, ∀ s, P.run rel j = some s → s.active.card ≤ K) :
    (P.runActive rel h).card ≤ (h+1)*K := by
  unfold runActive
  apply (card_biUnion_le).trans
  calc
    (∑ j ∈ range (h+1), (match P.run rel j with | none => ∅ | some s => s.active).card) ≤
        ∑ _j ∈ range (h+1), K := by
      apply sum_le_sum
      intro j hj
      cases hs : P.run rel j with
      | none => simp
      | some s => exact hb j (by simpa using hj) s hs
    _ = (h+1)*K := by simp

def PolynomiallyBounded (P : Machine R) : Prop :=
  ∃ c d : ℕ, ∀ (A : Type) (aFinite : Fintype A) (rel : R → A → A → Bool),
    ∃ h s, @Machine.run A R P aFinite rel h = some s ∧
      P.flag s .halt ∧ h+(P.runActive rel h).card ≤ c*(Fintype.card A+1)^d

end Machine

end

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

abbrev lift (e : A ≃ B) : HF A ≃ HF B := mapEquiv e

@[simp] lemma lift_empty (e : A ≃ B) : lift e empty = empty := map_ordinal e 0

@[simp] lemma lift_truth (e : A ≃ B) : lift e truth = truth := map_ordinal e 1

@[simp] lemma lift_ordinal (e : A ≃ B) (n : ℕ) : lift e (ordinal n) = ordinal n := map_ordinal e n

@[simp] lemma lift_double (e : A ≃ B) (x y : HF A) : lift e (double x y) = double (lift e x) (lift e y) := map_double e x y

@[simp] lemma lift_isSet (e : A ≃ B) (x : HF A) : isSet (lift e x) = isSet x := isSet_map e x

@[simp] lemma lift_boolean (e : A ≃ B) (p : Prop) : lift e (boolean p) = boolean p := by
  by_cases h : p <;> simp [boolean,h]

@[simp] lemma lift_truth_iff (e : A ≃ B) (x : HF A) : lift e x = truth ↔ x = truth := by
  rw [← lift_truth e,Equiv.apply_eq_iff_eq]

@[simp] lemma lift_empty_iff (e : A ≃ B) (x : HF A) : lift e x = empty ↔ x = empty := by
  rw [← lift_empty e,Equiv.apply_eq_iff_eq]

@[simp] lemma lift_mem_iff (e : A ≃ B) (x y : HF A) : lift e x ∈ lift e y ↔ x ∈ y := mem_mapEquiv e x y

lemma lift_elements (e : A ≃ B) (x : HF A) : elements (lift e x) = (elements x).image (lift e) := elements_map e x

lemma lift_ofFinset (e : A ≃ B) (s : Finset (HF A)) : lift e (ofFinset s) = ofFinset (s.image (lift e)) := map_ofFinset e s

lemma lift_allAtoms [Fintype A] [Fintype B] (e : A ≃ B) : lift e allAtoms = allAtoms := by
  rw [allAtoms,lift_ofFinset,allAtoms]
  congr 1
  ext x
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨e a,rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨atom (e.symm b),⟨e.symm b,rfl⟩,by simp [lift,mapEquiv]⟩

lemma lift_union (e : A ≃ B) (x : HF A) : lift e (unionHF x) = unionHF (lift e x) := by
  rw [unionHF,lift_ofFinset,unionHF,lift_elements]
  congr 1
  ext z
  simp only [mem_image,mem_biUnion]
  constructor
  · rintro ⟨z,⟨y,hy,hz⟩,rfl⟩
    exact ⟨lift e y,⟨y,hy,rfl⟩,(lift_mem_iff e z y).mpr hz⟩
  · rintro ⟨y,⟨w,hw,rfl⟩,hz⟩
    refine ⟨(lift e).symm z,⟨w,hw,?_⟩,Equiv.apply_symm_apply _ _⟩
    have := (lift_mem_iff e ((lift e).symm z) w).mp
    apply this
    simpa only [Equiv.apply_symm_apply] using (show z ∈ lift e w from hz)

lemma lift_unique (e : A ≃ B) (x : HF A) : lift e (uniqueHF x) = uniqueHF (lift e x) := by
  rcases uniqueHF_spec x with ⟨a,ha,hu⟩ | ⟨ha,hu⟩
  · have h : elements (lift e x) = {lift e a} := by rw [lift_elements,ha,image_singleton]
    rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · rw [hu,hv]
      exact singleton_injective (h.symm.trans hb)
    · exact (hb ⟨_,h⟩).elim
  · rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · exfalso
      apply ha
      refine ⟨(lift e).symm b,?_⟩
      apply (image_injective (lift e).injective)
      rw [← lift_elements,hb,image_singleton,Equiv.apply_symm_apply]
    · rw [hu,hv,lift_empty]

lemma lift_card (e : A ≃ B) (x : HF A) : lift e (cardinalityHF x) = cardinalityHF (lift e x) := by
  simp only [cardinalityHF,lift_ordinal,lift_elements,card_image_of_injective _ (lift e).injective]

lemma lift_input (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (r : R) (x y : HF A) :
    inputRelation rel' r (lift e x) (lift e y) ↔ inputRelation rel r x y := by
  constructor
  · rintro ⟨a,b,ha,hb,hr⟩
    refine ⟨e.symm a,e.symm b,?_,?_,?_⟩
    · apply (lift e).injective
      simpa [lift,mapEquiv] using ha
    · apply (lift e).injective
      simpa [lift,mapEquiv] using hb
    · simpa only [← hrel,Equiv.apply_symm_apply] using hr
  · rintro ⟨a,b,rfl,rfl,hr⟩
    exact ⟨e a,e b,rfl,rfl,by rw [hrel]; exact hr⟩

def locationEquiv (e : A ≃ B) : Location F arity A ≃ Location F arity B :=
  Equiv.sigmaCongrRight (fun _ => Equiv.piCongrRight (fun _ => lift e))

@[simp] lemma locationEquiv_apply (e : A ≃ B) (f : F) (v : Fin (arity f) → HF A) :
    locationEquiv e ⟨f,v⟩ = ⟨f,fun j => lift e (v j)⟩ := rfl

@[simp] lemma locationEquiv_symm_apply (e : A ≃ B) (f : F) (v : Fin (arity f) → HF B) :
    (locationEquiv e).symm ⟨f,v⟩ = ⟨f,fun j => (lift e).symm (v j)⟩ := rfl

namespace State

def transport (e : A ≃ B) (s : State F arity A) : State F arity B where
  value := fun l => lift e (s.value ((locationEquiv e).symm l))
  finite := by
    apply (s.finite.image (locationEquiv e)).subset
    intro l hl
    exact ⟨(locationEquiv e).symm l,by simpa using hl,Equiv.apply_symm_apply _ _⟩

@[simp] lemma transport_value (e : A ≃ B) (s : State F arity A) (l : Location F arity A) :
    (s.transport e).value (locationEquiv e l) = lift e (s.value l) := by
  simp [transport]

@[ext] lemma ext_value (s t : State F arity A) (h : ∀ l, s.value l = t.value l) : s = t := by
  cases s; cases t
  congr
  funext l
  exact h l

@[simp] lemma transport_initial (e : A ≃ B) : (initial : State F arity A).transport e = initial := by
  apply ext_value
  intro l
  simp [transport,initial]

end State

namespace Term

variable [Fintype A] [Fintype B]

lemma eval_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.eval rel' (s.transport e) (fun j => lift e (v j)) = lift e (t.eval rel s v) := by
  induction t with
  | var i => rfl
  | constant n => simp [eval]
  | atoms => simp [eval,lift_allAtoms]
  | app f args ih =>
    simp only [eval,ih]
    exact s.transport_value e ⟨f,fun j => (args j).eval rel s v⟩
  | pair a b ia ib => simp only [eval,ia,ib,lift_double]
  | union a ia => simp only [eval,ia,lift_union]
  | unique a ia => simp only [eval,ia,lift_unique]
  | card a ia => simp only [eval,ia,lift_card]
  | equal a b ia ib => simp only [eval,ia,ib,Equiv.apply_eq_iff_eq,lift_boolean]
  | member a b ia ib => simp only [eval,ia,ib,lift_mem_iff,lift_boolean]
  | isAtom a ia => simp only [eval,ia,lift_isSet,lift_boolean]
  | input r a b ia ib => simp only [eval,ia,ib,lift_input e rel rel' hrel,lift_boolean]
  | not a ia => simp only [eval,ia,ne_eq,lift_truth_iff,lift_boolean]
  | and a b ia ib => simp only [eval,ia,ib,lift_truth_iff,lift_boolean]
  | conditional c a b ic ia ib =>
    simp only [eval,ic,lift_truth_iff]
    split <;> simp_all
  | comprehension bound guard body ihb ihg iht =>
    simp only [eval,ihb,lift_elements,lift_ofFinset]
    congr 1
    ext z
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨z,⟨⟨x,hx,rfl⟩,hg⟩,hz⟩
      have hh : (lift e) ∘ (Fin.cons x v) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
        funext j; refine Fin.cases rfl (fun _ => rfl) j
      dsimp only [Function.comp_def] at hh
      rw [← hh,ihg,lift_truth_iff] at hg
      rw [← hh,iht] at hz
      exact ⟨body.eval rel s (Fin.cons x v),⟨x,⟨hx,hg⟩,rfl⟩,hz⟩
    · rintro ⟨z,⟨x,⟨hx,hg⟩,rfl⟩,hz⟩
      have hh : (lift e) ∘ (Fin.cons x v) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
        funext j; refine Fin.cases rfl (fun _ => rfl) j
      dsimp only [Function.comp_def] at hh
      exact ⟨lift e x,⟨⟨x,hx,rfl⟩,by rw [← hh,ihg,lift_truth_iff]; exact hg⟩,
        by rw [← hh,iht]; exact hz⟩

end Term

abbrev updateEquiv (e : A ≃ B) : Update F arity A ≃ Update F arity B :=
  Equiv.prodCongr (locationEquiv e) (lift e)

lemma mem_update_image (e : A ≃ B) (u : Finset (Update F arity A))
    (l : Location F arity A) (x : HF A) :
    (locationEquiv e l,lift e x) ∈ u.image (updateEquiv e) ↔ (l,x) ∈ u := by
  change updateEquiv e (l,x) ∈ _ ↔ _
  simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]

namespace Rule

variable [Fintype A] [Fintype B]

lemma updates_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) :
    r.updates rel' (s.transport e) (fun j => lift e (v j)) =
      (r.updates rel s v).image (updateEquiv e) := by
  induction r with
  | skip => simp [updates]
  | update f args value =>
    simp only [updates,Term.eval_transport e rel rel' hrel,image_singleton]
    rfl
  | parallel a b ia ib =>
    simp only [updates,ia,ib,image_union]
  | conditional c a b ia ib =>
    simp only [updates,Term.eval_transport e rel rel' hrel,lift_truth_iff]
    split <;> simp_all
  | «forall» bound body ih =>
    simp only [updates,Term.eval_transport e rel rel' hrel,lift_elements]
    rw [biUnion_image,image_biUnion]
    apply biUnion_congr rfl
    intro x hx
    have hcons : (lift e) ∘ Fin.cons x v = Fin.cons (lift e x) (fun j => lift e (v j)) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    dsimp only [Function.comp_def] at hcons
    rw [← hcons,ih]
  | letValue value body ih =>
    simp only [updates,Term.eval_transport e rel rel' hrel]
    have hcons : (lift e) ∘ Fin.cons (value.eval rel s v) v =
        Fin.cons (lift e (value.eval rel s v)) (fun j => lift e (v j)) := by
      funext j; refine Fin.cases rfl (fun _ => rfl) j
    dsimp only [Function.comp_def] at hcons
    rw [← hcons,ih]

end Rule

namespace State

lemma consistent_transport (e : A ≃ B) (u : Finset (Update F arity A)) :
    Consistent (u.image (updateEquiv e)) ↔ Consistent u := by
  constructor
  · intro h l x y hx hy
    apply (lift e).injective
    exact h _ _ _ ((mem_update_image e u l x).mpr hx) ((mem_update_image e u l y).mpr hy)
  · intro h l x y hx hy
    obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
    obtain ⟨x,rfl⟩ := (lift e).surjective x
    obtain ⟨y,rfl⟩ := (lift e).surjective y
    exact congrArg (lift e) (h _ _ _ ((mem_update_image e u l x).mp hx)
      ((mem_update_image e u l y).mp hy))

lemma applyUpdates_transport (e : A ≃ B) (s : State F arity A)
    (u : Finset (Update F arity A)) (hu : Consistent u) :
    (s.transport e).applyUpdates (u.image (updateEquiv e)) = (s.applyUpdates u).transport e := by
  apply ext_value
  intro l
  obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
  rw [transport_value]
  change (s.transport e).updatedValue (u.image (updateEquiv e)) (locationEquiv e l) =
    lift e (s.updatedValue u l)
  by_cases h : ∃ x, (l,x) ∈ u
  · obtain ⟨x,hx⟩ := h
    rw [s.updatedValue_eq u hu hx,
      updatedValue_eq _ _ ((consistent_transport e u).mpr hu) ((mem_update_image e u l x).mpr hx)]
  · rw [s.updatedValue_default u h,updatedValue_default]
    · exact s.transport_value e l
    · rintro ⟨x,hx⟩
      obtain ⟨x,rfl⟩ := (lift e).surjective x
      exact h ⟨x,(mem_update_image e u l x).mp hx⟩

lemma support_transport (e : A ≃ B) (s : State F arity A) :
    (s.transport e).support = s.support.image (locationEquiv e) := by
  ext l
  obtain ⟨l,rfl⟩ := (locationEquiv e).surjective l
  simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right,mem_support,transport_value,ne_eq,lift_empty_iff]

lemma critical_transport (e : A ≃ B) (s : State F arity A) :
    (s.transport e).critical = s.critical.image (lift e) := by
  simp only [critical,support_transport,biUnion_image,image_biUnion]
  apply biUnion_congr rfl
  intro l hl
  rw [transport_value,image_insert,image_image]
  cases l
  rfl

lemma active_transport [Fintype A] [Fintype B] (e : A ≃ B) (s : State F arity A) :
    (s.transport e).active = s.active.image (lift e) := by
  have hf : ∀ f : Finset (HF A), familyClosure (f.image (lift e)) = (familyClosure f).image (lift e) := by
    intro f
    simp only [familyClosure,biUnion_image,image_biUnion]
    apply biUnion_congr rfl
    intro x hx
    exact closure_map e x
  have ha : (univ.image (@atom B)).image ((lift e).symm) = univ.image (@atom A) := by
    ext x
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨e.symm b,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨atom (e a),⟨e a,rfl⟩,by simp [lift,mapEquiv]⟩
  have ha' : univ.image (@atom B) = (univ.image (@atom A)).image (lift e) := by
    rw [← ha,image_image]
    simp only [Function.comp_def,Equiv.apply_symm_apply,image_id']
  unfold active
  rw [critical_transport,ha',← hf]
  congr 1
  simp only [image_union,image_insert,image_singleton,lift_allAtoms,lift_empty,lift_truth]

end State

namespace Machine

variable (P : Machine R) [finiteA : Fintype A] [finiteB : Fintype B]

omit A B R P in
lemma flag_transport.{uDecl1, uDecl2, uDecl3}
    {A : Type uDecl1}
    {B : Type uDecl2}
    {R : Type uDecl3}
    (P : Operational.Machine R)
    [Fintype A]
    [Fintype B] (e : A ≃ B) (s : P.Store (A := A)) (c : Control) :
    P.flag (s.transport e) c ↔ P.flag s c := by
  have h : locationEquiv e (⟨Sum.inl c,Fin.elim0⟩ : Location _ P.functionArity A) =
      ⟨Sum.inl c,Fin.elim0⟩ := by
    change (⟨Sum.inl c,fun j : Fin 0 => lift e (Fin.elim0 j : HF A)⟩ : Location _ P.functionArity B) = ⟨Sum.inl c,Fin.elim0⟩
    congr 1
    funext i
    exact Fin.elim0 i
  unfold flag
  rw [← h,State.transport_value,lift_truth_iff]

lemma step_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : P.Store (A := A)) :
    P.step rel' (s.transport e) = (P.step rel s).map (State.transport e) := by
  have hv : (fun j : Fin 0 => lift e (Fin.elim0 j : HF A)) = Fin.elim0 := by
    funext j; exact Fin.elim0 j
  have hu := P.rule.updates_transport e rel rel' hrel s Fin.elim0
  rw [hv] at hu
  simp only [step,flag_transport,hu,State.consistent_transport]
  split
  · rfl
  · split
    · rename_i hc
      simp only [Option.map_some]
      congr 1
      exact State.applyUpdates_transport e s _ hc
    · rfl

lemma run_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (j : ℕ) :
    P.run rel' j = (P.run rel j).map (State.transport e) := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
    simp only [run,ih]
    cases hs : P.run rel j with
    | none => rfl
    | some s => exact P.step_transport e rel rel' hrel s

lemma runActive_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (h : ℕ) :
    P.runActive rel' h = (P.runActive rel h).image (lift e) := by
  unfold runActive
  rw [biUnion_image]
  apply biUnion_congr rfl
  intro j hj
  rw [P.run_transport e rel rel' hrel]
  cases hs : P.run rel j with
  | none => simp
  | some s => exact s.active_transport e

end Machine

end CPTSeparation.Operational

namespace CPTSeparation.Hereditary

open Classical Finset

variable {A : Type*}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

lemma closure_ofFinset (s : Finset (HF A)) :
    closure (ofFinset s) = insert (ofFinset s) (familyClosure s) := by
  rw [closure,elements_ofFinset]
  congr 1
  ext x
  simp [familyClosure]

lemma closure_subset_of_transitive {s : Finset (HF A)}
    (hs : ∀ x ∈ s, ∀ y, y ∈ x → y ∈ s) {x : HF A} (hx : x ∈ s) : closure x ⊆ s := by
  intro y hy
  have h := (mem_closure_iff y x).mp hy
  clear hy
  induction h with
  | refl => exact hx
  | @tail b c h hbc ih => exact ih (hs c hx b hbc)

lemma elements_subset_closure (x : HF A) : elements x ⊆ closure x := by
  intro y hy
  exact closure_member_subset hy (mem_closure_self y)

lemma closure_atom (a : A) : closure (atom a) = {atom a} := by
  rw [closure,elements_atom]
  simp

lemma closure_double_subset (x y : HF A) :
    closure (double x y) ⊆ insert (double x y) (closure x ∪ closure y) := by
  rw [double,closure_ofFinset]
  intro z hz
  simp only [mem_insert,mem_union] at hz ⊢
  rcases hz with h | h
  · exact Or.inl h
  · obtain ⟨w,hw,hz⟩ := mem_familyClosure.mp h
    have he : w = x ∨ w = y := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw
    rcases he with he | he
    · rw [he] at hz; exact Or.inr (Or.inl hz)
    · rw [he] at hz; exact Or.inr (Or.inr hz)

lemma closure_ordinal (n : ℕ) : closure (ordinal (A := A) n) = (range (n+1)).image ordinal := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [closure]
    ext x
    simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists,mem_image,mem_range]
    constructor
    · rintro (rfl | ⟨y,hy,hx⟩)
      · exact ⟨n,by omega,rfl⟩
      · obtain ⟨j,hj,rfl⟩ := (mem_ordinal y n).mp hy
        rw [ih j hj] at hx
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
        exact ⟨k,by simp only [mem_range] at hk; omega,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      by_cases he : j = n
      · exact Or.inl (by rw [he])
      · exact Or.inr ⟨ordinal j,(mem_ordinal _ _).mpr ⟨j,by omega,rfl⟩,mem_closure_self _⟩

lemma card_closure_ordinal (n : ℕ) : (closure (ordinal (A := A) n)).card = n+1 := by
  rw [closure_ordinal,card_image_of_injective _ (fun _ _ h => ordinal_injective h),card_range]

end CPTSeparation.Hereditary

namespace CPTSeparation.Operational

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

lemma closure_union_subset (x : HF A) : closure (unionHF x) ⊆ insert (unionHF x) (closure x) := by
  rw [unionHF,closure_ofFinset]
  apply insert_subset_insert
  intro z hz
  obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
  obtain ⟨w,hw,hyw⟩ := mem_biUnion.mp hy
  exact (closure_member_subset hw) ((closure_member_subset hyw) hzy)

lemma closure_unique_subset (x : HF A) : closure (uniqueHF x) ⊆ insert empty (closure x) := by
  rcases uniqueHF_spec x with ⟨a,ha,hu⟩ | ⟨ha,hu⟩
  · rw [hu]
    exact (closure_member_subset (by change a ∈ elements x; rw [ha]; simp)).trans (subset_insert _ _)
  · rw [hu,closure_ordinal]
    simp

lemma card_closure_card (x : HF A) : (closure (cardinalityHF x)).card ≤ (closure x).card+1 := by
  rw [cardinalityHF,card_closure_ordinal]
  exact Nat.add_le_add_right (card_le_card (elements_subset_closure x)) 1

lemma card_closure_boolean (p : Prop) : (closure (boolean (A := A) p)).card ≤ 2 := by
  by_cases h : p <;> simp [boolean,h,truth,empty,card_closure_ordinal]

namespace State

variable [Fintype A]

lemma empty_mem_active (s : State F arity A) : empty ∈ s.active := by
  apply familyClosure_contains
  simp []

lemma atoms_mem_active (s : State F arity A) : allAtoms ∈ s.active := by
  apply familyClosure_contains
  simp []

lemma closure_value_subset_active (s : State F arity A) (l : Location F arity A) :
    closure (s.value l) ⊆ s.active := by
  apply closure_subset_of_transitive (fun x hx y hy => s.active_transitive hx hy)
  by_cases h : s.value l = empty
  · rw [h]; exact s.empty_mem_active
  · apply familyClosure_contains
    exact mem_union_left _ (mem_union_left _ (s.value_mem_critical h))

lemma closure_atoms_subset_active (s : State F arity A) : Hereditary.closure allAtoms ⊆ s.active :=
  closure_subset_of_transitive (fun _ hx _ hy => s.active_transitive hx hy) s.atoms_mem_active

end State

namespace Term

variable [Fintype A]

def trace (rel : R → A → A → Bool) (s : State F arity A) :
    {k : ℕ} → Term R F arity k → (Fin k → HF A) → Finset (HF A)
  | _, .var i,v => closure (v i)
  | _, .constant n,_ => closure (ordinal n)
  | _, .atoms,_ => closure allAtoms
  | _, .app f args,v => closure (s.value ⟨f,fun j => (args j).eval rel s v⟩) ∪
      univ.biUnion (fun j => trace rel s (args j) v)
  | _, .pair a b,v => closure (double (a.eval rel s v) (b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .union a,v => closure (unionHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .unique a,v => closure (uniqueHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .card a,v => closure (cardinalityHF (a.eval rel s v)) ∪ trace rel s a v
  | _, .equal a b,v => closure (boolean (a.eval rel s v = b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .member a b,v => closure (boolean (a.eval rel s v ∈ b.eval rel s v)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .isAtom a,v => closure (boolean (isSet (a.eval rel s v) = false)) ∪ trace rel s a v
  | _, .input r a b,v => closure (boolean (inputRelation rel r (a.eval rel s v) (b.eval rel s v))) ∪ trace rel s a v ∪ trace rel s b v
  | _, .not a,v => closure (boolean (a.eval rel s v ≠ truth)) ∪ trace rel s a v
  | _, .and a b,v => closure (boolean (a.eval rel s v = truth ∧ b.eval rel s v = truth)) ∪ trace rel s a v ∪ trace rel s b v
  | _, .conditional c a b,v => trace rel s c v ∪ trace rel s a v ∪ trace rel s b v
  | _, .comprehension bound guard body,v =>
      insert (ofFinset (((elements (bound.eval rel s v)).filter
        (fun x => guard.eval rel s (Fin.cons x v) = truth)).image
        (fun x => body.eval rel s (Fin.cons x v))))
      (trace rel s bound v ∪ (elements (bound.eval rel s v)).biUnion
        (fun x => trace rel s guard (Fin.cons x v) ∪ trace rel s body (Fin.cons x v)))

lemma closure_eval_subset_trace (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    closure (t.eval rel s v) ⊆ t.trace rel s v := by
  induction t with
  | var i => exact Subset.rfl
  | constant n => exact Subset.rfl
  | atoms => exact Subset.rfl
  | app f args ih => exact subset_union_left
  | pair a b _ _ => exact subset_union_left.trans subset_union_left
  | union a _ => exact subset_union_left
  | unique a _ => exact subset_union_left
  | card a _ => exact subset_union_left
  | equal a b _ _ => exact subset_union_left.trans subset_union_left
  | member a b _ _ => exact subset_union_left.trans subset_union_left
  | isAtom a _ => exact subset_union_left
  | input r a b _ _ => exact subset_union_left.trans subset_union_left
  | not a _ => exact subset_union_left
  | and a b _ _ => exact subset_union_left.trans subset_union_left
  | conditional c a b _ ia ib =>
    simp only [eval]
    split
    · exact (ia v).trans (subset_union_right.trans subset_union_left)
    · exact (ib v).trans subset_union_right
  | comprehension bound guard body ihb ihg iht =>
    simp only [eval,trace,closure_ofFinset]
    apply insert_subset_insert
    intro z hz
    obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,(mem_filter.mp hx).1,
      mem_union_right _ (iht _ hzy)⟩)

def bound : {k : ℕ} → Term R F arity k → Polynomial ℕ
  | _, .var _ => .X
  | _, .constant n => .C (n+1)
  | _, .atoms => .X
  | _, .app _ args => .X + ∑ j, bound (args j)
  | _, .pair a b => 1 + 2 * (bound a + bound b)
  | _, .union a => 1 + 2 * bound a
  | _, .unique a => 1 + 2 * bound a
  | _, .card a => 1 + 2 * bound a
  | _, .equal a b => 2 + bound a + bound b
  | _, .member a b => 2 + bound a + bound b
  | _, .isAtom a => 2 + bound a
  | _, .input _ a b => 2 + bound a + bound b
  | _, .not a => 2 + bound a
  | _, .and a b => 2 + bound a + bound b
  | _, .conditional c a b => bound c + bound a + bound b
  | _, .comprehension b g t => 1 + bound b + bound b *
      ((bound g).comp (.X + bound b) + (bound t).comp (.X + bound b))

def potential {k : ℕ} (s : State F arity A) (v : Fin k → HF A) : ℕ :=
  s.active.card + ∑ j, (closure (v j)).card

lemma potential_var {k : ℕ} (s : State F arity A) (v : Fin k → HF A) (j : Fin k) :
    (closure (v j)).card ≤ potential s v := by
  unfold potential
  exact (single_le_sum (s := (univ : Finset (Fin k))) (f := fun j => (closure (v j)).card)
    (fun _ _ => Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left _ _)

lemma potential_active {k : ℕ} (s : State F arity A) (v : Fin k → HF A) :
    s.active.card ≤ potential s v := Nat.le_add_right _ _

lemma potential_cons {k : ℕ} (s : State F arity A) (v : Fin k → HF A) (x : HF A) :
    potential s (Fin.cons x v) = potential s v + (closure x).card := by
  simp only [potential,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  omega

lemma card_trace_le (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) (K : ℕ) (hK : potential s v ≤ K) :
    (t.trace rel s v).card ≤ t.bound.eval K := by
  induction t generalizing K with
  | var j => simpa only [trace,bound,Polynomial.eval_X] using (potential_var s v j).trans hK
  | constant n => simpa only [trace,bound,Polynomial.eval_C] using (card_closure_ordinal (A := A) n).le
  | atoms => simpa only [trace,bound,Polynomial.eval_X] using
      (card_le_card s.closure_atoms_subset_active).trans ((potential_active s v).trans hK)
  | app f args ih =>
    unfold trace bound
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_finsetSum]
    calc
      _ ≤ (closure (s.value ⟨f,fun j => (args j).eval rel s v⟩)).card +
          ∑ j, ((args j).trace rel s v).card :=
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
      _ ≤ K + ∑ j, (args j).bound.eval K := add_le_add
        ((card_le_card (s.closure_value_subset_active _)).trans ((potential_active s v).trans hK))
        (sum_le_sum (fun j _ => ih j v K hK))
  | pair a b ia ib =>
    have ha := ia v K hK; have hb := ib v K hK
    have ha' := card_le_card (closure_eval_subset_trace rel s a v)
    have hb' := card_le_card (closure_eval_subset_trace rel s b v)
    have hp := card_le_card (closure_double_subset (a.eval rel s v) (b.eval rel s v))
    have hp' := card_insert_le (double (a.eval rel s v) (b.eval rel s v))
      (closure (a.eval rel s v) ∪ closure (b.eval rel s v))
    have hcu := card_union_le (closure (a.eval rel s v)) (closure (b.eval rel s v))
    have ht := card_union_le (closure (double (a.eval rel s v) (b.eval rel s v)) ∪ a.trace rel s v) (b.trace rel s v)
    have ht' := (card_union_le (closure (double (a.eval rel s v) (b.eval rel s v))) (a.trace rel s v))
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | union a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_le_card (closure_union_subset (a.eval rel s v))
    have hi := card_insert_le (unionHF (a.eval rel s v)) (closure (a.eval rel s v))
    have hu := card_union_le (closure (unionHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | unique a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_le_card (closure_unique_subset (a.eval rel s v))
    have hi := card_insert_le (empty (A := A)) (closure (a.eval rel s v))
    have hu := card_union_le (closure (uniqueHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | card a ia =>
    have ha := ia v K hK
    have hc := card_le_card (closure_eval_subset_trace rel s a v)
    have hp := card_closure_card (a.eval rel s v)
    have hu := card_union_le (closure (cardinalityHF (a.eval rel s v))) (a.trace rel s v)
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  | equal a b ia ib | member a b ia ib | input r a b ia ib | and a b ia ib =>
    have ha := ia v K hK; have hb := ib v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_union_le _ _) (le_refl _)).trans
    apply (add_le_add (add_le_add (card_closure_boolean _) ha) hb).trans
    simp only [bound,Polynomial.eval_add,Polynomial.eval_ofNat,le_refl]
  | isAtom a ia | not a ia =>
    have ha := ia v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_closure_boolean _) ha).trans
    simp only [bound,Polynomial.eval_add,Polynomial.eval_ofNat,le_refl]
  | conditional c a b ic ia ib =>
    have hc := ic v K hK; have ha := ia v K hK; have hb := ib v K hK
    unfold trace
    apply (card_union_le _ _).trans
    apply (add_le_add (card_union_le _ _) (le_refl _)).trans
    simp only [bound,Polynomial.eval_add]
    omega
  | comprehension b g t ib ig it =>
    have hb := ib v K hK
    have hc := (card_le_card (elements_subset_closure (b.eval rel s v))).trans
      ((card_le_card (closure_eval_subset_trace rel s b v)).trans hb)
    have hsub (x) (hx : x ∈ elements (b.eval rel s v)) :
        potential s (Fin.cons x v) ≤ K + b.bound.eval K := by
      rw [potential_cons]
      apply add_le_add hK
      exact (card_le_card ((closure_member_subset hx).trans
        (closure_eval_subset_trace rel s b v))).trans hb
    have hi := card_insert_le (s := (trace rel s b v ∪ (elements (b.eval rel s v)).biUnion
        (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v))))
      (ofFinset (((elements (b.eval rel s v)).filter
        (fun x => g.eval rel s (Fin.cons x v) = truth)).image
        (fun x => t.eval rel s (Fin.cons x v))))
    have hu := card_union_le (trace rel s b v) ((elements (b.eval rel s v)).biUnion
        (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v)))
    have hbi := @card_biUnion_le (HF A) (HF A) _ (elements (b.eval rel s v))
      (fun x => trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v))
    have hsum := sum_le_card_nsmul (elements (b.eval rel s v))
      (fun x => (trace rel s g (Fin.cons x v) ∪ trace rel s t (Fin.cons x v)).card)
      (g.bound.eval (K+b.bound.eval K) + t.bound.eval (K+b.bound.eval K)) (by
        intro x hx
        exact (card_union_le _ _).trans (add_le_add (ig _ _ (hsub x hx)) (it _ _ (hsub x hx))))
    simp only [nsmul_eq_mul, Nat.cast_id] at hsum
    have hm := Nat.mul_le_mul_right (g.bound.eval (K+b.bound.eval K) + t.bound.eval (K+b.bound.eval K)) hc
    simp only [trace,bound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Term

end CPTSeparation.Operational

end

end OAI
