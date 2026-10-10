import OAI.Computability.WitnessedChoice.EncodedCounting

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations Quantitative Filter

lemma atomSizeConstant_pos : 0 < atomSizeConstant := by
  unfold atomSizeConstant localSizeBound
  positivity

theorem exists_numeric_box (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      let N : ℕ := atomSizeConstant*(n+1)^3
      let s : ℕ := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
      let M : ℕ := palette (n+1:ℝ)
      2 ≤ N ∧ 0 < s ∧ max 4 (m+1)*s ≤ M ∧
      (7:ℝ)*((max 2 m*s:ℕ):ℝ)+7*((6*((max 2 m*s:ℕ):ℝ))/boxConstant)^((3:ℝ)/2)+1 ≤ M ∧
      GiantBound n M := by
  have hC : 0 < (atomSizeConstant:ℝ) := by exact_mod_cast atomSizeConstant_pos
  have hev := eventual_bounds (atomSizeConstant:ℝ) (q:ℝ) boxConstant hC boxConstant_pos m
  have ht : Filter.Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have he := ht.eventually hev
  obtain ⟨n,hn,hnum⟩ := ((eventually_ge_atTop (1:ℕ)).and he).exists
  refine ⟨n,hn,?_⟩
  dsimp only
  let N : ℕ := atomSizeConstant*(n+1)^3
  have hN : 2 ≤ N := by
    have hC' : 1 ≤ atomSizeConstant := atomSizeConstant_pos
    have hp : 2 ≤ (n+1)^3 := by
      have h := Nat.pow_le_pow_left (show 2 ≤ n+1 by omega) 3
      norm_num at h
      omega
    exact hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n+1)^3) hC')
  have hlog : 0 < Real.logb 3 (N:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
  have hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    apply Nat.ceil_pos.mpr
    have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hrad : radius (atomSizeConstant:ℝ) (q:ℝ) (n+1:ℝ) =
      ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    simp only [radius,N,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [hrad] at hnum
  refine ⟨hN,hs,?_,?_,?_⟩
  · exact_mod_cast hnum.1
  · simpa only [N,Nat.cast_mul, Nat.cast_max, Nat.cast_ofNat] using hnum.2.1
  · simpa only [GiantBound,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hnum.2.2

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation

def structureQuery (A : Interpretations.Structure Symbol) : Prop :=
  Input.query ({ rel := A.rel } : Input A.Carrier)

namespace Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations Quantitative

theorem program_agrees_on_some_box (P : Program Symbol) (hP : P.polynomiallyBounded) :
    ∃ (n : ℕ) (_hn : 1 ≤ n) (vstar : Vertex n),
      P.accepts (programInput (0 : Vertex n → Scalar)) ↔
        P.accepts (programInput (Pi.single vstar 1)) := by
  obtain ⟨c,d,hcost⟩ := hP
  obtain ⟨m,hm,wiδ,wiη,wiρ,wsδ,wsη,wsρ,wh,wo⟩ := P.exists_width
  let q := traceExponent c d
  have hq : 0 < q := by dsimp [q,traceExponent]; omega
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^timeExponent c d
  let vstar : Vertex n := ⟨0,0,0⟩
  let S := fun i => programInput (twoCharges vstar i)
  have hN : 2 ≤ N := hnum.1
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1
  have hinput : ∀ i, Fintype.card (S i).Carrier ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hbInput : ∀ i, Nat.card (Atom (twoCharges vstar i)) ≤ B := by
    intro i
    apply le_trans _ (polynomial_bounds c d N hN).2.1
    simpa only [Nat.card_eq_fintype_card] using hinput i
  have hcostB (i : Bool) : ∃ j, P.haltsAt (S i) j ∧ P.cost (S i) j ≤ B := by
    obtain ⟨j,hj,hc⟩ := hcost (S i)
    refine ⟨j,hj,hc.trans ?_⟩
    calc
      c*(Fintype.card (S i).Carrier+1)^d ≤ c*(N+1)^d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hinput i) 1) d)
      _ ≤ B := (polynomial_bounds c d N hN).2.2.1
  obtain ⟨j,hj,hjc⟩ := hcostB false
  obtain ⟨k,hk,hkc⟩ := hcostB true
  let K := min j k+1
  have hK : K ≤ B := (by omega : K ≤ j+1).trans ((P.stage_le_cost (S false) j).trans hjc)
  have hsize : ∀ i l, l < K → Nat.card (P.state (programInput (twoCharges vstar i)) l).Carrier ≤ B := by
    intro i l hl
    cases i
    · exact (P.size_le_cost (S false) (by omega : l ≤ j)).trans hjc
    · exact (P.size_le_cost (S true) (by omega : l ≤ k)).trans hkc
  have hpoly : (9*B^3:ℝ) ≤ (N:ℝ)^(q:ℝ) := by
    simpa only [B,q,Nat.cast_pow] using real_trace_bound c d N hN
  have hagree (l : ℕ) (hl : l ≤ min j k) (ψ : Interpretations.Formula P.StateSymbols 0)
      (hw : ψ.scopedWidth < m) :
      ψ.holds (P.state (S false) l) ↔ ψ.holds (P.state (S true) l) := by
    exact stage_sentence_agrees (N := N) P vstar hn hB hK (by omega) hbInput hsize (q:ℝ)
      (by positivity) hpoly hm wiδ wiη wiρ wsδ wsη wsρ
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2 (by omega : l < K) ψ hw
  exact ⟨n,hn,vstar,(P.synchronize (S false) (S true) hj hk
    (fun l hl => hagree l hl P.halt wh) (fun l hl => hagree l hl P.output wo)).2⟩

end

end Grid

theorem query_not_interpretation_definable :
    Interpretations.NondefinableByInterpretations structureQuery := by
  rintro ⟨P,hpoly,hdecides⟩
  obtain ⟨n,hn,vstar,hagree⟩ := Grid.program_agrees_on_some_box P hpoly
  obtain ⟨hzero,hunit⟩ := Grid.opposite_answers hn vstar
  apply hunit
  exact (hdecides _).mp (hagree.mp ((hdecides _).mpr hzero))

end WitnessedSeparation



namespace WitnessedSeparation.Operational

noncomputable section

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

abbrev empty : HF A := ordinal 0

abbrev truth : HF A := ordinal 1

def boolean (p : Prop) : HF A := if p then truth else empty

@[simp] theorem truth_ne_empty : (truth : HF A) ≠ empty :=
  fun h => by have := ordinal_injective h; omega

@[simp] theorem boolean_truth (p : Prop) : boolean (A := A) p = truth ↔ p := by
  by_cases h : p <;> simp [boolean,h,Ne.symm truth_ne_empty]

def inputRelation (rel : R → A → A → Bool) (r : R) (x y : HF A) : Prop :=
  ∃ a b, x = atom a ∧ y = atom b ∧ rel r a b = true

def allAtoms [Fintype A] : HF A := ofFinset (univ.image atom)

def unionHF (x : HF A) : HF A := ofFinset ((elements x).biUnion elements)

def uniqueHF (x : HF A) : HF A :=
  if h : ∃ a, elements x = {a} then h.choose else empty

lemma uniqueHF_spec (x : HF A) :
    (∃ a, elements x = {a} ∧ uniqueHF x = a) ∨
      (¬ ∃ a, elements x = {a}) ∧ uniqueHF x = empty := by
  by_cases h : ∃ a, elements x = {a}
  · exact Or.inl ⟨h.choose,h.choose_spec,by simp only [uniqueHF,dite_eq_left h]⟩
  · exact Or.inr ⟨h,by simp only [uniqueHF,dite_eq_right h]⟩

def cardinalityHF (x : HF A) : HF A := ordinal (elements x).card

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

abbrev Location (F : Type*) (arity : F → ℕ) (A : Type*) := Σ f : F, Fin (arity f) → HF A

abbrev Valuation := Location F arity A → HF A

structure State (F : Type*) (arity : F → ℕ) (A : Type*) where
  value : Location F arity A → HF A
  finite : Set.Finite {l | value l ≠ empty}

namespace State

def initial : State F arity A := ⟨fun _ => empty, by simp⟩

def support (s : State F arity A) : Finset (Location F arity A) := s.finite.toFinset

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

abbrev Update (F : Type*) (arity : F → ℕ) (A : Type*) := Location F arity A × HF A

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

def Consistent (u : Finset (Update F arity A)) : Prop :=
  ∀ l x y, (l,x) ∈ u → (l,y) ∈ u → x = y

def updatedValue (s : State F arity A) (u : Finset (Update F arity A))
    (l : Location F arity A) : HF A :=
  if h : ∃ x, (l,x) ∈ u then h.choose else s.value l

lemma updatedValue_eq (s : State F arity A) (u : Finset (Update F arity A))
    (hu : Consistent u) {l : Location F arity A} {x : HF A} (hx : (l,x) ∈ u) :
    s.updatedValue u l = x := by
  have h : ∃ y, (l,y) ∈ u := ⟨x,hx⟩
  simp only [updatedValue,dite_eq_left h]
  exact hu l _ _ h.choose_spec hx

lemma updatedValue_default (s : State F arity A) (u : Finset (Update F arity A))
    {l : Location F arity A} (hl : ¬ ∃ x, (l,x) ∈ u) : s.updatedValue u l = s.value l := by
  simp only [updatedValue,dite_eq_right hl]

def applyUpdates (s : State F arity A) (u : Finset (Update F arity A)) : State F arity A where
  value := s.updatedValue u
  finite := by
    apply (s.finite.union (u.image Prod.fst).finite_toSet).subset
    intro l hl
    by_cases h : ∃ x, (l,x) ∈ u
    · obtain ⟨x,hx⟩ := h
      exact Or.inr (mem_image.mpr ⟨(l,x),hx,rfl⟩)
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq,updatedValue,dite_eq_right h] using hl)

end State

inductive Control | halt | accept deriving DecidableEq

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

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A B : Type*}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

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

def familyClosure (f : Finset (HF A)) : Finset (HF A) := f.biUnion closure

lemma mem_familyClosure {f : Finset (HF A)} {x : HF A} :
    x ∈ familyClosure f ↔ ∃ y ∈ f, x ∈ closure y := by simp [familyClosure]

lemma familyClosure_contains {f : Finset (HF A)} {x : HF A} (hx : x ∈ f) :
    x ∈ familyClosure f := mem_familyClosure.mpr ⟨x,hx,mem_closure_self x⟩

lemma familyClosure_transitive {f : Finset (HF A)} {x y : HF A}
    (hx : x ∈ familyClosure f) (hy : y ∈ x) : y ∈ familyClosure f := by
  obtain ⟨z,hz,hxz⟩ := mem_familyClosure.mp hx
  exact mem_familyClosure.mpr ⟨z,hz,closure_transitive hxz hy⟩

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Operational

noncomputable section

open Classical Hereditary Finset

variable {A R F : Type*} {arity : F → ℕ}

local instance {C : Type*} : DecidableEq (HF C) := Classical.decEq _

namespace State

def critical (s : State F arity A) : Finset (HF A) :=
  s.support.biUnion (fun l => insert (s.value l) (univ.image l.2))

lemma value_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) : s.value l ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_self _ _⟩

lemma argument_mem_critical (s : State F arity A) {l : Location F arity A}
    (h : s.value l ≠ empty) (i : Fin (arity l.1)) : l.2 i ∈ s.critical := by
  exact mem_biUnion.mpr ⟨l,(mem_support s l).mpr h,mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,rfl⟩)⟩

def active [Fintype A] (s : State F arity A) : Finset (HF A) :=
  familyClosure (s.critical ∪ {allAtoms,empty,truth} ∪ univ.image atom)

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





noncomputable section

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

variable (P : Machine R) [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma flag_transport (e : A ≃ B) (s : P.Store (A := A)) (c : Control) :
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

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Hereditary

noncomputable section

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

end

end WitnessedSeparation.Hereditary

end OAI
