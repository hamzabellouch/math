import OAI.ModelTheory.Choiceless.Definability

namespace OAI

noncomputable section

namespace CPTSeparation.Operational

section

open Classical Hereditary Finset

variable {A R F : Type} {arity : F → ℕ} [finiteA : Fintype A]

local instance {B : Type} : DecidableEq (HF B) := Classical.decEq _

def Closed (t : Finset (HF A)) : Prop := ∀ x ∈ t, ∀ y, y ∈ x → y ∈ t

namespace Closed

omit A in
lemma closure
    {A : Type}
    [Fintype A] (x : HF A) : Closed (Hereditary.closure x) := fun _ hx _ hy => closure_transitive hx hy

omit A in
lemma union
    {A : Type}
    [Fintype A] {s t : Finset (HF A)} (hs : Closed s) (ht : Closed t) : Closed (s ∪ t) := by
  intro x hx y hy
  rcases mem_union.mp hx with hx | hx
  · exact mem_union_left _ (hs x hx y hy)
  · exact mem_union_right _ (ht x hx y hy)

omit A in
lemma biUnion
    {A : Type}
    [Fintype A] {I : Type} (s : Finset I) (t : I → Finset (HF A)) (h : ∀ i ∈ s, Closed (t i)) : Closed (s.biUnion t) := by
  intro x hx y hy
  obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨i,hi,h i hi x hx y hy⟩

omit A in
lemma insert
    {A : Type}
    [Fintype A] {s : Finset (HF A)} {x : HF A} (hs : Closed s) (hx : ∀ y, y ∈ x → y ∈ s) : Closed (insert x s) := by
  intro y hy z hz
  rcases mem_insert.mp hy with rfl | hy
  · exact mem_insert_of_mem (hx z hz)
  · exact mem_insert_of_mem (hs y hy z hz)

end Closed

namespace Term

lemma trace_closed (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) : Closed (t.trace rel s v) := by
  induction t with
  | var i | constant n | atoms => exact Closed.closure _
  | app f args ih => exact (Closed.closure _).union (Closed.biUnion univ _ (fun j _ => ih j v))
  | pair a b ia ib | equal a b ia ib | member a b ia ib | input r a b ia ib | and a b ia ib =>
    exact ((Closed.closure _).union (ia v)).union (ib v)
  | union a ia | unique a ia | card a ia | isAtom a ia | not a ia => exact (Closed.closure _).union (ia v)
  | conditional c a b ic ia ib => exact ((ic v).union (ia v)).union (ib v)
  | comprehension b g t ib ig it =>
    apply Closed.insert ((ib v).union (Closed.biUnion _ _ (fun x hx => (ig _).union (it _))))
    intro y hy
    rw [mem_ofFinset] at hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,(mem_filter.mp hx).1,mem_union_right _ (closure_eval_subset_trace rel s t _ (mem_closure_self _))⟩)

end Term

namespace Rule

lemma trace_closed (rel : R → A → A → Bool) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) : Closed (r.trace rel s v) := by
  induction r with
  | skip => intro x hx; exact (Finset.notMem_empty x hx).elim
  | update f args value => exact (value.trace_closed rel s v).union (Closed.biUnion univ _ (fun j _ => (args j).trace_closed rel s v))
  | parallel r t ir it => exact (ir v).union (it v)
  | conditional c r t ir it => exact ((c.trace_closed rel s v).union (ir v)).union (it v)
  | «forall» b r ih => exact (b.trace_closed rel s v).union (Closed.biUnion _ _ (fun x hx => ih _))
  | letValue b r ih => exact (b.trace_closed rel s v).union (ih _)

end Rule

end

section

open Classical Hereditary Counting HFCoding Finset

variable {A R F : Type} {arity : F → ℕ}

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

namespace State

lemma value_apply_iff (d : Set (HF A)) (s : State F arity A) (u : Finset (Update F arity A))
    (hc : Consistent u) (hv : ∀ l z, (l,z) ∈ u → z ∈ d)
    (l : Location F arity A) (z : Domain d) :
    z.val = (s.applyUpdates u).value l ↔
      (l,z.val) ∈ u ∨ (z.val = s.value l ∧ ¬∃ x : Domain d, (l,x.val) ∈ u) := by
  change z.val = s.updatedValue u l ↔ _
  by_cases hu : ∃ x, (l,x) ∈ u
  · obtain ⟨x,hx⟩ := hu
    rw [s.updatedValue_eq u hc hx]
    constructor
    · intro he; exact Or.inl (he ▸ hx)
    · rintro (h | ⟨_,h⟩)
      · exact hc l _ _ h hx
      · exact (h ⟨⟨x,hv l x hx⟩,hx⟩).elim
  · rw [s.updatedValue_default u hu]
    constructor
    · intro h; exact Or.inr ⟨h,fun ⟨x,hx⟩ => hu ⟨x.val,hx⟩⟩
    · rintro (h | ⟨h,_⟩)
      · exact (hu ⟨z.val,h⟩).elim
      · exact h

end State

variable {ι L : Type} {B : ι → Type} [finiteFamilyB : ∀ i, Fintype (B i)]

variable (d : ∀ i, Set (HF (B i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := B i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → B i → B i → Bool) (s : ∀ i, State F arity (B i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_updates (K : ℕ) (r : Rule R F arity 0) (f : F)
    (hm : arity f+1+r.width ≤ m)
    (ht : ∀ i x, x ∈ r.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K) :
    UniformDefinable S m (arity f+1) (fun i v =>
      (⟨f,fun j => (v j.succ).val⟩,(v 0).val) ∈ r.updates (rel i) (s i) Fin.elim0) := by
  have h := Rule.uniform_graph d S hd hp ha hmem hset rel s hinput hstate K r f
    (0 : Fin (arity f+1)) Fin.succ Fin.elim0 hm
  apply h.congr
  intro i v
  have he : (fun j : Fin 0 => (v (Fin.elim0 j)).val) = Fin.elim0 := by funext j; exact Fin.elim0 j
  constructor
  · intro h
    have hh := Rule.graph_sound (d i) K (rel i) (s i) (hd i) r f (v 0) (v ∘ Fin.succ) (v ∘ Fin.elim0) h
    simpa only [Function.comp_apply,he] using hh
  · intro h
    apply Rule.graph_complete (d i) K (rel i) (s i) (hd i) r f (v 0) (v ∘ Fin.succ) (v ∘ Fin.elim0)
    · simpa only [Function.comp_apply,he] using ht i
    · simpa only [Function.comp_apply,he] using h

omit F arity ι L B d S m s hstate in
lemma uniform_applyUpdates
    {F : Type}
    {arity : F → ℕ}
    {ι : Type}
    {L : Type}
    {B : ι → Type}
    [(i : ι) → Fintype (B i)]
    (d : (i : ι) → Set (Hereditary.HF (B i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (s : (i : ι) → Operational.State F arity (B i))
    (hstate : ∀ (f : F),
  Counting.UniformDefinable S m (arity f + 1) fun i v => ↑(v 0) = (s i).value ⟨f, fun j => ↑(v j.succ)⟩) (u : ∀ i, Finset (Update F arity (B i)))
    (hu : ∀ f, UniformDefinable S m (arity f+1) (fun i v =>
      (⟨f,fun j => (v j.succ).val⟩,(v 0).val) ∈ u i))
    (hc : ∀ i, State.Consistent (u i))
    (hv : ∀ i l z, (l,z) ∈ u i → z ∈ d i)
    (f : F) (hm : arity f+1 < m) :
    UniformDefinable S m (arity f+1) (fun i v =>
      (v 0).val = ((s i).applyUpdates (u i)).value ⟨f,fun j => (v j.succ).val⟩) := by
  have hx := (hu f).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (arity f+1) → Fin (arity f+2))
  have hx' := hx.ex hm
  apply ((hu f).or ((hstate f).and hx'.neg)).congr
  intro i v
  have he := State.value_apply_iff (d i) (s i) (u i) (hc i) (hv i)
    ⟨f,fun j => (v j.succ).val⟩ (v 0)
  simp only [Fin.cons_zero,Fin.cons_succ,Function.comp_apply] at *
  exact he.symm

end

open Classical Hereditary Finset

variable {A B R F : Type} {arity : F → ℕ} [finiteA : Fintype A] [finiteB : Fintype B]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

omit A B in
lemma lift_closure
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B] (e : A ≃ B) (x : HF A) : closure (lift e x) = (closure x).image (lift e) := closure_map e x

omit A B in
lemma lift_cons
    {A : Type}
    {B : Type}
    [Fintype A]
    [Fintype B] (e : A ≃ B) {k : ℕ} (x : HF A) (v : Fin k → HF A) :
    (fun j => lift e ((Fin.cons x v : Fin (k+1) → HF A) j)) = Fin.cons (lift e x) (fun j => lift e (v j)) := by
  funext j; refine Fin.cases rfl (fun _ => rfl) j

namespace Term

lemma trace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (t : Term R F arity k) (v : Fin k → HF A) :
    t.trace rel' (s.transport e) (fun j => lift e (v j)) = (t.trace rel s v).image (lift e) := by
  have hev {k} (t : Term R F arity k) (v : Fin k → HF A) := eval_transport e rel rel' hrel s t v
  induction t with
  | var j => exact lift_closure e _
  | constant n => simp only [trace,← lift_ordinal e n,lift_closure]
  | atoms => rw [trace,trace,← lift_allAtoms e,lift_closure]
  | app f args ih =>
    simp only [trace,hev,ih,image_union,biUnion_image]
    rw [show (s.transport e).value ⟨f,fun j => lift e ((args j).eval rel s v)⟩ = lift e (s.value ⟨f,fun j => (args j).eval rel s v⟩) from s.transport_value e ⟨f,fun j => (args j).eval rel s v⟩,lift_closure]
  | pair a b ia ib => simp only [trace,hev,ia,ib,image_union,← lift_double,lift_closure]
  | union a ia => simp only [trace,hev,ia,image_union,← lift_union,lift_closure]
  | unique a ia => simp only [trace,hev,ia,image_union,← lift_unique,lift_closure]
  | card a ia => simp only [trace,hev,ia,image_union,← lift_card,lift_closure]
  | equal a b ia ib => simp only [trace,hev,ia,ib,image_union,Equiv.apply_eq_iff_eq,← lift_boolean e,lift_closure]
  | member a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_mem_iff,← lift_boolean e,lift_closure]
  | isAtom a ia => simp only [trace,hev,ia,image_union,lift_isSet,← lift_boolean e,lift_closure]
  | input r a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_input e rel rel' hrel,← lift_boolean e,lift_closure]
  | not a ia => simp only [trace,hev,ia,image_union,ne_eq,lift_truth_iff,← lift_boolean e,lift_closure]
  | and a b ia ib => simp only [trace,hev,ia,ib,image_union,lift_truth_iff,← lift_boolean e,lift_closure]
  | conditional c a b ic ia ib => simp only [trace,ic,ia,ib,image_union]
  | comprehension b g t ib ig it =>
    have hz := hev (comprehension b g t) v
    change insert ((comprehension b g t).eval rel' (s.transport e) _) _ = Finset.image (lift e) (insert ((comprehension b g t).eval rel s v) _)
    rw [hz,image_insert]
    congr 1
    simp only [ib,hev,lift_elements,biUnion_image,image_union,image_biUnion,biUnion_image]
    congr 1
    apply biUnion_congr rfl
    intro x hx
    rw [← lift_cons e x v,ig,it]

end Term

namespace Rule

lemma trace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (s : State F arity A)
    {k : ℕ} (r : Rule R F arity k) (v : Fin k → HF A) :
    r.trace rel' (s.transport e) (fun j => lift e (v j)) = (r.trace rel s v).image (lift e) := by
  have ht {k} (t : Term R F arity k) (v : Fin k → HF A) := t.trace_transport e rel rel' hrel s v
  have he {k} (t : Term R F arity k) (v : Fin k → HF A) := t.eval_transport e rel rel' hrel s v
  induction r with
  | skip => simp only [trace,image_empty]
  | update f args value => simp only [trace,ht,image_union,biUnion_image]
  | parallel r t ir it => simp only [trace,ir,it,image_union]
  | conditional c r t ir it => simp only [trace,ht,ir,it,image_union]
  | «forall» b r ih =>
    simp only [trace,ht,he,image_union,lift_elements,biUnion_image,image_biUnion]
    congr 1
    apply biUnion_congr rfl
    intro x hx
    rw [← lift_cons e x v,ih]
  | letValue b r ih =>
    simp only [trace,ht,he,image_union]
    rw [← lift_cons e (b.eval rel s v) v,ih]

end Rule

end CPTSeparation.Operational

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, P.Store (A := A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (P.functionArity f+1)
  (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

omit R ι L A P d S m hd hp hmem hset s hstate in
lemma uniform_flag
    {R : Type}
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (P : Operational.Machine R)
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ}
    (hd : ∀ (i : ι), ∀ x ∈ d i, ∀ y ∈ x, y ∈ d i)
    (hp : ∀ (i : ι) (k : ℕ), Hereditary.ordinal k ∈ d i)
    (hmem : Counting.UniformDefinable S m 2 fun _ v => (v 0).val ∈ (v 1).val)
    (hset : Counting.UniformDefinable S m 1 fun _ v => Hereditary.isSet (v 0).val = true)
    (s : (i : ι) → P.Store (A := A i))
    (hstate : ∀ (f : Operational.Control ⊕ P.Functions),
  Counting.UniformDefinable S m (P.functionArity f + 1) fun i v =>
    ↑(v 0) = (s i).value ⟨f, fun j => ↑(v j.succ)⟩) (hm : 6 ≤ m) (c : Control) :
    UniformDefinable S m 0 (fun i _ => P.flag (s i) c) := by
  have ht := HFCoding.uniform_ordinal S hmem hset hm hd hp 1
  have hs := hstate (Sum.inl c)
  simp only [functionArity,Sum.elim_inl] at hs
  have hs' : UniformDefinable S m 1 (fun i v => (v 0).val = (s i).value ⟨Sum.inl c,Fin.elim0⟩) := by
    apply hs.congr
    intro i v
    have hh : (fun j : Fin 0 => (v j.succ).val) = Fin.elim0 := by funext j; exact Fin.elim0 j
    rw [hh]
    rfl
  apply (hs'.and ht).ex (by omega) |>.congr
  intro i v
  change (∃ x : Domain (d i), x.val = (s i).value ⟨Sum.inl c,_⟩ ∧ x.val = truth) ↔ _
  constructor
  · rintro ⟨x,hx,hxt⟩
    exact hx.symm.trans hxt
  · intro h
    exact ⟨⟨truth,hp i 1⟩,h.symm,rfl⟩

include hd hp ha hmem hset hinput hstate in
lemma uniform_step (K : ℕ) (s' : ∀ i, P.Store (A := A i))
    (hh : ∀ i, P.step (rel i) (s i) = some (s' i))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m)
    (hroom : 6 ≤ m)
    (ht : ∀ i x, x ∈ P.rule.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K)
    (f : Control ⊕ P.Functions) :
    UniformDefinable S m (P.functionArity f+1) (fun i v =>
      (v 0).val = (s' i).value ⟨f,fun j => (v j.succ).val⟩) := by
  have hu (f) := uniform_updates d S hd hp ha hmem hset rel s hinput hstate K P.rule f (by have := hm f; omega) ht
  have hx := ((hu f).reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (P.functionArity f+1) → Fin (P.functionArity f+2))).ex (by have := hm f; omega)
  have hadd := (hu f).or ((hstate f).and hx.neg)
  have hhalt := (uniform_flag P d S hd hp hmem hset s hstate hroom .halt).reindex (Fin.elim0 : Fin 0 → Fin (P.functionArity f+1))
  apply ((hhalt.and (hstate f)).or (hhalt.neg.and hadd)).congr
  intro i v
  have hh' := hh i
  by_cases hf : P.flag (s i) .halt
  · have he : s i = s' i := Option.some.inj (by simpa only [step,ite_eq_left hf] using hh')
    simp only [hf,true_and,not_true_eq_false,false_and,or_false]
    rw [he]
  · have hc : State.Consistent (P.rule.updates (rel i) (s i) Fin.elim0) := by
      by_contra hc
      simp only [step,ite_eq_right hf,ite_eq_right hc] at hh'
      contradiction
    have he : (s i).applyUpdates (P.rule.updates (rel i) (s i) Fin.elim0) = s' i := Option.some.inj (by simpa only [step,ite_eq_right hf,ite_eq_left hc] using hh')
    have hv : ∀ l z, (l,z) ∈ P.rule.updates (rel i) (s i) Fin.elim0 → z ∈ d i := by
      intro l z hz
      exact (ht i z ((P.rule.closure_update_subset_trace (rel i) (s i) Fin.elim0 hz).1 (mem_closure_self z))).1
    have hvv := State.value_apply_iff (d i) (s i) _ hc hv ⟨f,fun j => (v j.succ).val⟩ (v 0)
    rw [he] at hvv
    simp only [hf,false_and,not_false_eq_true,true_and,false_or,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    exact hvv.symm

end

section

open Classical Hereditary Finset

variable {A B R : Type} [Fintype A] [Fintype B]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R)

def runTrace (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  P.runActive rel h ∪ (range (h+1)).biUnion (fun j => match P.run rel j with
    | none => ∅
    | some s => P.rule.trace rel s Fin.elim0)

lemma rule_trace_subset (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) :
    P.rule.trace rel s Fin.elim0 ⊆ P.runTrace rel h := by
  intro x hx
  exact mem_union_right _ (mem_biUnion.mpr ⟨j,by simpa using hj,by simpa only [hs] using hx⟩)

lemma active_subset_trace (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
    (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.runTrace rel h :=
  (P.state_active_subset rel hj hs).trans subset_union_left

lemma runTrace_closed (rel : R → A → A → Bool) (h : ℕ) : Closed (P.runTrace rel h) := by
  apply Closed.union (fun _ hx _ hy => P.runActive_transitive rel h hx hy)
  apply Closed.biUnion
  intro j hj
  cases hs : P.run rel j with
  | none => intro x hx; exact (notMem_empty _ hx).elim
  | some s => exact P.rule.trace_closed rel s Fin.elim0

lemma card_runTrace_le (rel : R → A → A → Bool) (h K : ℕ)
    (hb : ∀ j ≤ h, ∀ s, P.run rel j = some s → s.active.card ≤ K) :
    (P.runTrace rel h).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
  have hc : ((range (h+1)).biUnion (fun j => match P.run rel j with
    | none => ∅ | some s => P.rule.trace rel s Fin.elim0)).card ≤ (h+1)*P.rule.bound.eval K := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _j ∈ range (h+1), P.rule.bound.eval K := by
        apply sum_le_sum
        intro j hj
        cases hs : P.run rel j with
        | none => simp
        | some s =>
          apply P.rule.card_trace_le rel s Fin.elim0 K
          simpa only [Term.potential,Finset.univ_eq_empty,Finset.sum_empty,Nat.add_zero] using hb j (by simpa using hj) s hs
      _ = _ := by simp
  exact (card_union_le _ _).trans (by
    have ha := P.runActive_card_le rel h K hb
    nlinarith)

lemma runTrace_transport (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (h : ℕ) :
    P.runTrace rel' h = (P.runTrace rel h).image (lift e) := by
  unfold runTrace
  rw [P.runActive_transport e rel rel' hrel,image_union,biUnion_image]
  congr 1
  apply biUnion_congr rfl
  intro j hj
  rw [P.run_transport e rel rel' hrel]
  cases hs : P.run rel j with
  | none => simp
  | some s =>
    have hv : (fun j : Fin 0 => lift e (Fin.elim0 j : HF A)) = Fin.elim0 := by funext j; exact Fin.elim0 j
    simpa only [Option.map_some,hv] using P.rule.trace_transport e rel rel' hrel s Fin.elim0

end

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_run (ss : ∀ i, ℕ → P.Store (A := A i)) (h K : ℕ)
    (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
      x ∈ d i ∧ (elements x).card ≤ K) :
    ∀ f, UniformDefinable S m (P.functionArity f+1)
      (fun i v => (v 0).val = (ss i h).value ⟨f,fun j => (v j.succ).val⟩) := by
  induction h with
  | zero =>
    intro f
    have hz := (HFCoding.uniform_ordinal S hmem hset hroom hd hp 0).reindex
      (fun _ : Fin 1 => (0 : Fin (P.functionArity f+1)))
    apply hz.congr
    intro i v
    have he : State.initial = ss i 0 := Option.some.inj (hr i 0 (by omega))
    rw [← he]
    rfl
  | succ h ih =>
    have hs := ih (fun i j hj => hr i j (by omega)) (fun i j hj => ht i j (by omega))
    apply P.uniform_step d S hd hp ha hmem hset rel (fun i => ss i h) hinput hs K (fun i => ss i (h+1))
    · intro i
      have hh := hr i (h+1) (by omega)
      simpa only [run,hr i h (by omega),Option.bind_some] using hh
    · exact hm
    · exact hroom
    · intro i x hx
      exact ht i h (by omega) x hx

include hd hp ha hmem hset hinput in
lemma uniform_run_flag (ss : ∀ i, ℕ → P.Store (A := A i)) (h K : ℕ)
    (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
      x ∈ d i ∧ (elements x).card ≤ K) (c : Control) :
    UniformDefinable S m 0 (fun i _ => P.flag (ss i h) c) :=
  P.uniform_flag d S hd hp hmem hset (fun i => ss i h)
    (P.uniform_run d S hd hp ha hmem hset rel hinput ss h K hr hm hroom ht) hroom c

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n : ℕ} (b : Vertex n → Scalar) (P : Operational.Machine Symbol)

lemma opTrace_supported (hn : 1 ≤ n) (h K N : ℕ) (hN : 0 < N)
    (ha : ∀ j ≤ h, ∀ st, P.run (atomInput b).rel j = some st → st.active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q) :
    ∀ x ∈ P.runTrace (atomInput b).rel h,
      HereditarilySupported (G := CentralGroup n) ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ x := by
  have hi : ∀ g : BoxGroup n, ∀ x ∈ P.runTrace (atomInput b).rel h,
      g • x ∈ P.runTrace (atomInput b).rel h := by
    intro g x hx
    have ht := P.runTrace_transport (actionIso (b := b) g).toEquiv
      (atomInput b).rel (atomInput b).rel (fun r a b => (actionIso g).rel_eq r a b) h
    have hm : g • x ∈ (P.runTrace (atomInput b).rel h).image (lift (actionIso (b := b) g).toEquiv) :=
      mem_image.mpr ⟨x,hx,rfl⟩
    exact (congrArg (fun t : Finset (HF (Atom b)) => g • x ∈ t) ht).mpr hm

  apply invariant_family_hereditarily_supported hn _ hi (P.runTrace_closed _ h) N hN q hq
  have hc : ((P.runTrace (atomInput b).rel h).card : ℝ) ≤ ((h+1)*(K+P.rule.bound.eval K):ℝ) := by
    exact_mod_cast P.card_runTrace_le (atomInput b).rel h K ha
  exact hc.trans hb

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

lemma program_atom_mem (hs : 0 < s) (i : ι) (a : Atom (bs i)) :
    atom a ∈ programDomain bs (s := s) i := by
  apply hereditary_iff.mpr
  constructor
  · refine ⟨fun _ => a,?_⟩
    intro g hg
    rw [smul_atom,hg ⟨0,hs⟩]
  · intro y hy
    have hh : y ∈ (∅ : Finset (HF (Atom (bs i)))) := hy
    exact (notMem_empty _ hh).elim

lemma op_input_uniform (r : Symbol) :
    UniformDefinable (programHF bs (s := s)) m 2
      (fun i v => inputRelation (atomInput (bs i)).rel r (v 0).val (v 1).val) := by
  apply (UniformDefinable.relation (S := programHF bs) (.base (.input r)) 0 1).congr
  intro i v
  change (∃ a b, (v 0).val = atom a ∧ (v 1).val = atom b ∧ AtomRelation (bs i) r a b) ↔ _
  simp only [inputRelation,atomInput,decide_eq_true_eq]

end

open Classical Hereditary Counting HFCoding Operational Finset

local instance instDecidableEqHF2 {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_flag_agrees (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) (c : Control) :
    P.flag (ss false h) c ↔ P.flag (ss true h) c := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ P.runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) P hn h K N hN (hbound i) q hq hb
  have ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := P.rule_trace_subset (atomInput (twoCharges vstar i)).rel (Nat.le_of_lt hj) (hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ P.runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact P.runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans (P.card_runTrace_le _ h K (hbound i))
  have hd := P.uniform_run_flag D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h ((h+1)*(K+P.rule.bound.eval K)) hr hm hroom ht c
  obtain ⟨φ,hφ,hφsem⟩ := hd (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  exact (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))

end CPTSeparation.Grid

namespace CPTSeparation.PolynomialCost

open Finset

lemma eval_bound (p : Polynomial ℕ) : ∃ c d : ℕ, ∀ K, p.eval K ≤ c*(K+1)^d := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨c,d,hp⟩ := hp
    obtain ⟨e,f,hr⟩ := hr
    refine ⟨c+e,d+f,fun K => ?_⟩
    rw [Polynomial.eval_add]
    have h1 : (K+1)^d ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (K+1)^f ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      p.eval K + r.eval K ≤ c*(K+1)^d + e*(K+1)^f := add_le_add (hp K) (hr K)
      _ ≤ c*(K+1)^(d+f)+e*(K+1)^(d+f) := add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  | monomial n a =>
    refine ⟨a,n,fun K => ?_⟩
    rw [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) n)

end CPTSeparation.PolynomialCost

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R)

lemma run_none (rel : R → A → A → Bool) {j : ℕ} (hj : P.run rel j = none) :
    ∀ k, j ≤ k → P.run rel k = none := by
  intro k hk
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction l with
  | zero => simpa using hj
  | succ l ih =>
    change (P.run rel (j+l)).bind (P.step rel) = none
    rw [ih]
    rfl

lemma run_prefix_exists (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) {j : ℕ} (hj : j ≤ h) : ∃ t, P.run rel j = some t := by
  cases hs : P.run rel j with
  | some t => exact ⟨t,rfl⟩
  | none => have he := P.run_none rel hs h hj; rw [hh] at he; contradiction

lemma halted_persists (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) (hf : P.flag s .halt) :
    ∀ k, h ≤ k → P.run rel k = some s := by
  intro k hk
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction l with
  | zero => simpa using hh
  | succ l ih =>
    change (P.run rel (h+l)).bind (P.step rel) = some s
    rw [ih]
    simp only [Option.bind_some,step,ite_eq_left hf]

lemma run_total_of_halts (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) (hf : P.flag s .halt) (j : ℕ) :
    ∃ t, P.run rel j = some t := by
  by_cases hj : j ≤ h
  · exact P.run_prefix_exists rel hh hj
  · exact ⟨s,P.halted_persists rel hh hf j (by omega)⟩

lemma active_card_of_halts (rel : R → A → A → Bool) {h : ℕ} {s : P.Store (A := A)}
    (hh : P.run rel h = some s) (hf : P.flag s .halt) {j : ℕ} {t : P.Store (A := A)}
    (hj : P.run rel j = some t) : t.active.card ≤ (P.runActive rel h).card := by
  by_cases hjh : j ≤ h
  · exact card_le_card (P.state_active_subset rel hjh hj)
  · have he := P.halted_persists rel hh hf j (by omega)
    have ht : t = s := Option.some.inj (hj.symm.trans he)
    subst t
    exact card_le_card (P.state_active_subset rel (le_refl h) hh)

lemma flag_accept_eq_of_halts (rel : R → A → A → Bool) {h j : ℕ} {s t : P.Store (A := A)}
    (hh : P.run rel h = some s) (hf : P.flag s .halt)
    (hj : P.run rel j = some t) (hjh : h ≤ j) :
    P.accepts rel ↔ P.flag t .accept := by
  have he : t = s := Option.some.inj (hj.symm.trans (P.halted_persists rel hh hf j hjh))
  subst t
  constructor
  · rintro ⟨k,u,hk,huf,hua⟩
    by_cases hkh : k ≤ h
    · have ht := P.halted_persists rel hk huf h hkh
      have he : u = s := Option.some.inj (ht.symm.trans hh)
      exact he ▸ hua
    · have ht := P.halted_persists rel hh hf k (by omega)
      have he : u = s := Option.some.inj (hk.symm.trans ht)
      exact he ▸ hua
  · intro ha; exact ⟨h,s,hh,hf,ha⟩

end

open Classical Finset

variable {R : Type} (P : Machine R)

lemma exists_palette : ∃ m : ℕ, 6 ≤ m ∧ ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
  let := P.finiteFunctions
  let total := ∑ f : Control ⊕ P.Functions, P.functionArity f
  refine ⟨total+P.rule.width+8,by omega,?_⟩
  intro f
  have hf : P.functionArity f ≤ total := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ f)
  omega

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

theorem operational_agrees_on_some_box (P : Operational.Machine Symbol) (hP : P.PolynomiallyBounded) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (vstar : Vertex n),
      P.accepts (atomInput (0 : Vertex n → Scalar)).rel ↔
        P.accepts (atomInput (Pi.single vstar 1)).rel := by
  obtain ⟨c,d,hcost⟩ := hP
  obtain ⟨m,hroom,hm⟩ := P.exists_palette
  let p : Polynomial ℕ := (Polynomial.X+1)*(Polynomial.X+P.rule.bound)
  obtain ⟨cp,dp,hp⟩ := PolynomialCost.eval_bound p
  let e := timeExponent c d
  let a := timeExponent cp dp
  let q := e*a
  have he : 2 ≤ e := timeExponent_ge_two c d
  have ha : 2 ≤ a := timeExponent_ge_two cp dp
  have hq : 0 < q := Nat.mul_pos (by omega) (by omega)
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^e
  let vstar : Vertex n := ⟨0,0,0⟩
  let rel := fun i => (atomInput (twoCharges vstar i)).rel
  have hN : 2 ≤ N := hnum.1
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1
  have hinput : ∀ i, Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hcostB (i : Bool) : ∃ j st, P.run (rel i) j = some st ∧ P.flag st .halt ∧
      j+(P.runActive (rel i) j).card ≤ B := by
    obtain ⟨j,st,hj,hf,hc⟩ := hcost (Atom (twoCharges vstar i)) inferInstance (rel i)
    refine ⟨j,st,hj,hf,hc.trans ?_⟩
    exact (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right (hinput i) 1) d)).trans
      (polynomial_bounds c d N hN).2.2.1
  choose jj tt hrun hhalt hbudget using hcostB
  let h := max (jj false) (jj true)
  have hjh (i : Bool) : jj i ≤ h := by cases i <;> simp only [h,le_max_left,le_max_right]
  have hhB : h ≤ B := max_le (by have := hbudget false; omega) (by have := hbudget true; omega)
  have htotal : ∀ i j, ∃ st, P.run (rel i) j = some st :=
    fun i j => P.run_total_of_halts (rel i) (hrun i) (hhalt i) j
  choose ss hrs using htotal
  have hactive : ∀ i j, (ss i j).active.card ≤ B := by
    intro i j
    exact (P.active_card_of_halts (rel i) (hrun i) (hhalt i) (hrs i j)).trans (by have := hbudget i; omega)
  have hpoly : (h+1)*(B+P.rule.bound.eval B) ≤ N^q := by
    calc
      (h+1)*(B+P.rule.bound.eval B) ≤ (B+1)*(B+P.rule.bound.eval B) := Nat.mul_le_mul_right _ (by omega)
      _ = p.eval B := by simp only [p,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      _ ≤ cp*(B+1)^dp := hp B
      _ ≤ B^a := (polynomial_bounds cp dp B hB).2.2.1
      _ = N^q := by simp only [B,q,pow_mul]
  have hh := op_flag_agrees (N := N) P vstar hn h B (by omega) ss
    (fun i j _ => hrs i j) (fun i j _ => hactive i j) (q:ℝ) (by positivity)
    (by rw [Real.rpow_natCast]; exact_mod_cast hpoly) hm hroom
    hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2 .accept
  refine ⟨n,hn,vstar,?_⟩
  exact (P.flag_accept_eq_of_halts (rel false) (hrun false) (hhalt false) (hrs false h) (hjh false)).trans
    (hh.trans (P.flag_accept_eq_of_halts (rel true) (hrun true) (hhalt true) (hrs true h) (hjh true)).symm)

end CPTSeparation.Grid

namespace CPTSeparation

theorem query_not_intrinsically_bounded_HF :
    ¬ ∃ P : Operational.Machine Symbol, P.PolynomiallyBounded ∧
      ∀ (A : Type) (fA : Fintype A) (S : Input A), @Input.query A fA S ↔ @Operational.Machine.accepts A Symbol P fA S.rel := by
  rintro ⟨P,hP,hdecides⟩
  obtain ⟨n,hn,vstar,hagree⟩ := Grid.operational_agrees_on_some_box P hP
  obtain ⟨hz,hu⟩ := Grid.opposite_answers hn vstar
  apply hu
  exact (hdecides _ _ _).mpr (hagree.mp ((hdecides _ _ _).mp hz))

end CPTSeparation

end

end OAI
