import Mathlib
import OAI.Combinatorics.StripMass.StepComplete

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

namespace Graph

 

structure WireContraction {V W : Type*} {n : ℕ} (r : V → V → Prop) (s : W → W → Prop)
    (a : Fin n → V) (b : Fin n → W) where
  project : V → W
  core : W → V
  section_eq : ∀ v, project (core v)=v
  map_edge : ∀ v w, r v w → Relation.ReflTransGen s (project v) (project w)
  core_edge : ∀ v w, s v w → r (core v) (core w)
  map_boundary : ∀ i, project (a i)=b i
  boundary_injective : Function.Injective b
  map_used : ∀ v, Used r v → Used s (project v)
  retract : ∀ v, Used r v → Relation.ReflTransGen r v (core (project v))
  boundary_retract : ∀ i, Used s (b i) → Relation.ReflTransGen r (core (b i)) (a i)

namespace WireContraction
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W} [Std.Symm r] [Std.Symm s]

theorem lift_boundary_reach (e : WireContraction r s a b) {i j : Fin n}
    (hij : i≠j) (h : Relation.ReflTransGen s (b i) (b j)) :
    Relation.ReflTransGen r (a i) (a j) := by
  have hne : b i≠b j := fun hh => hij (e.boundary_injective hh)
  have hi := Graph.used_of_reach_ne h hne
  have hj := Graph.used_of_reach_ne (symm h) hne.symm
  have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) h
  exact ((symm (e.boundary_retract i hi)).trans hm).trans (e.boundary_retract j hj)

theorem realizes (e : WireContraction r s a b) {p : Pairing n}
    (h : GraphRealizes r a p) : GraphRealizes s b p := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.core v) (e.core w) (e.core_edge v w hvw)
    have hm := Graph.map_reach e.project e.map_edge hr
    rw [e.section_eq,e.map_boundary] at hm
    exact ⟨i,hi,hm⟩
  · intro i j
    constructor
    · intro hr
      by_cases hij : i=j
      · exact Or.inl hij
      · exact (h.reach i j).mp (e.lift_boundary_reach hij hr)
    · intro hh
      have hm := Graph.map_reach e.project e.map_edge ((h.reach i j).mpr hh)
      rwa [e.map_boundary,e.map_boundary] at hm

theorem realizes_inv (e : WireContraction r s a b) {p : Pairing n}
    (h : GraphRealizes s b p) : GraphRealizes r a p := by
  constructor
  · intro v w hvw
    obtain ⟨x,hx⟩ := e.map_used v ⟨w,hvw⟩
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.project v) x hx
    have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) hr
    have hb := (h.boundary_used_iff e.boundary_injective i).mpr hi
    exact ⟨i,hi,((e.retract v ⟨w,hvw⟩).trans hm).trans (e.boundary_retract i hb)⟩
  · intro i j
    constructor
    · intro hr
      have hm := Graph.map_reach e.project e.map_edge hr
      rw [e.map_boundary,e.map_boundary] at hm
      exact (h.reach i j).mp hm
    · intro hh
      rcases hh with hij | hadj
      · subst j; exact .refl
      · have hij : i≠j := by intro hh; subst j; exact p.adj_irrefl i hadj
        exact e.lift_boundary_reach hij ((h.reach i j).mpr (Or.inr hadj))

theorem realizes_iff (e : WireContraction r s a b) {p : Pairing n} :
    GraphRealizes r a p ↔ GraphRealizes s b p := ⟨e.realizes,e.realizes_inv⟩

end WireContraction
end Graph

 

 

section LocalContractions
open scoped Classical

namespace CompactGate
variable {V : Type*} {n : ℕ}

def wiring (r : V → V → Prop) (boundary : Fin n → V) (active : Fin n → Prop)
    (a b : Fin n) (t : Tile) : Sum V (Fin 4) → Sum V (Fin 4) → Prop
  | .inl v, .inl w => r v w
  | .inr k, .inr l => t.Adj k l
  | .inl v, .inr k | .inr k, .inl v =>
      (v=boundary a ∧ k=0 ∧ active a) ∨ (v=boundary b ∧ k=1 ∧ active b)

def boundary (old : Fin n → V) (a b : Fin n) (i : Fin n) : Sum V (Fin 4) :=
  if i=a then .inr 2 else if i=b then .inr 3 else .inl (old i)

def project (old : Fin n → V) (a b : Fin n) : Sum V (GateExterior n) → Sum V (Fin 4)
  | .inl v => .inl v
  | .inr (.inl k) => .inr k
  | .inr (.inr i) => boundary old a b i

def core : Sum V (Fin 4) → Sum V (GateExterior n)
  | .inl v => .inl v
  | .inr k => .inr (.inl k)

@[simp] theorem project_core (old : Fin n → V) (a b : Fin n) (v : Sum V (Fin 4)) :
    project old a b (core v)=v := by cases v <;> rfl

@[simp] theorem boundary_left (old : Fin n → V) (a b : Fin n) : boundary old a b a=.inr 2 := by
  simp [boundary]
@[simp] theorem boundary_right (old : Fin n → V) (a b : Fin n) (hab : a≠b) :
    boundary old a b b=.inr 3 := by simp [boundary,hab.symm]

theorem boundary_injective (old : Fin n → V) (h : Function.Injective old)
    (a b : Fin n) : Function.Injective (boundary old a b) := by
  intro i j hij
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp_all [boundary]
  exact h hij

instance wiring_symm (r : V → V → Prop) [Std.Symm r] (old : Fin n → V)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Std.Symm (wiring r old active a b t) := by
  constructor
  intro v w h
  cases v <;> cases w <;> try exact h
  · change r _ _ at h ⊢; exact symm h
  · exact h.elim Or.inr Or.inl

end CompactGate

namespace Patch
instance glued_symm {A B I : Type*} (r : A → A → Prop) (s : B → B → Prop)
    [Std.Symm r] [Std.Symm s] (a : I → A) (b : I → B) (active : I → Prop) :
    Std.Symm (glued r s a b active) := by
  constructor
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => change r _ _ at h ⊢; exact symm h
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
  | inr v =>
    cases w with
    | inl w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
    | inr w => change s _ _ at h ⊢; exact symm h
end Patch

instance gateWiring_symm {n : ℕ} (a b : Fin n) (t : Tile) : Std.Symm (gateWiring a b t) := by
  constructor
  intro v w h
  rcases v with k | i <;> rcases w with l | j <;> try exact h
  exact h.elim Or.inr Or.inl

namespace CompactGate
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin n → V} {p : Pairing n}

abbrev full (a b : Fin n) (t : Tile) :=
  Patch.glued r (gateWiring a b t) old (gateInput a b) p.Occupied

omit [Std.Symm r] in
lemma core_edge (a b : Fin n) (hab : a≠b) (t : Tile) (v w : Sum V (Fin 4))
    (h : wiring r old p.Occupied a b t v w) : full (r:=r) (old:=old) (p:=p) a b t (core v) (core w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact h
    | inr k =>
      rcases h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩
      · exact ⟨a,ha,rfl,by simp [gateInput]⟩
      · exact ⟨b,hb,rfl,by simp [gateInput,hab.symm]⟩
  | inr k =>
    cases w with
    | inl v =>
      rcases h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩
      · exact ⟨a,ha,by simp [gateInput],rfl⟩
      · exact ⟨b,hb,by simp [gateInput,hab.symm],rfl⟩
    | inr l => exact h

omit [Std.Symm r] in
lemma project_edge (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : Sum V (GateExterior n)) (h : full (r:=r) (old:=old) (p:=p) a b t v w) :
    Relation.ReflTransGen (wiring r old p.Occupied a b t) (project old a b v) (project old a b w) := by
  rcases v with v | (k | i) <;> rcases w with w | (l | j)
  · exact .single h
  · obtain ⟨i,hi,rfl,he⟩ := h
    rcases (gateInput_eq_box a b i hab l).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · exact .single (Or.inr ⟨rfl,rfl,hi⟩)
  · obtain ⟨i,hi,rfl,he⟩ := h
    obtain ⟨rfl,hia,hib⟩ := (gateInput_eq_out a b i j).mp he.symm
    simp only [project,boundary,ite_eq_right hia,ite_eq_right hib]
    exact .refl
  · obtain ⟨i,hi,he,rfl⟩ := h
    rcases (gateInput_eq_box a b i hab k).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · exact .single (Or.inr ⟨rfl,rfl,hi⟩)
  · exact .single h
  · rcases h with ⟨hia,rfl,_⟩ | ⟨hib,rfl,_⟩
    · subst j; simp only [project,boundary_left]; exact .refl
    · subst j; simp only [project,boundary_right old a b hab]; exact .refl
  · obtain ⟨j,hj,he,rfl⟩ := h
    obtain ⟨rfl,hia,hib⟩ := (gateInput_eq_out a b j i).mp he.symm
    simp only [project,boundary,ite_eq_right hia,ite_eq_right hib]
    exact .refl
  · rcases h with ⟨hia,rfl,_⟩ | ⟨hib,rfl,_⟩
    · subst i; simp only [project,boundary_left]; exact .refl
    · subst i; simp only [project,boundary_right old a b hab]; exact .refl
  · exact h.elim

omit [Std.Symm r] in
lemma used_old_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (t : Tile) (v : V) :
    Graph.Used (wiring r old p.Occupied a b t) (.inl v) ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr k =>
      rcases hw with ⟨rfl,_,ha⟩ | ⟨rfl,_,hb⟩
      · exact (hp.boundary_used_iff hinj a).mpr ha
      · exact (hp.boundary_used_iff hinj b).mpr hb
  · rintro ⟨w,hw⟩; exact ⟨.inl w,hw⟩

omit [Std.Symm r] in
lemma used_output_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n) :
    Graph.Used (wiring r old p.Occupied a b t) (boundary old a b i) ↔ p.stepSupport a b t i := by
  by_cases hia : i=a
  · subst i
    rw [boundary_left]
    simp only [Pairing.stepSupport,ite_true,eq_self]
    constructor
    · rintro ⟨v,hv⟩
      cases v with
      | inl v => rcases hv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> have hh := congrArg Fin.val h <;> norm_num at hh
      | inr k => exact ⟨k,hv⟩
    · rintro ⟨k,hk⟩; exact ⟨.inr k,hk⟩
  · by_cases hib : i=b
    · subst i
      rw [boundary_right old a b hab]
      simp only [Pairing.stepSupport,ite_eq_right hia,ite_true,eq_self]
      constructor
      · rintro ⟨v,hv⟩
        cases v with
        | inl v => rcases hv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> have hh := congrArg Fin.val h <;> norm_num at hh
        | inr k => exact ⟨k,hv⟩
      · rintro ⟨k,hk⟩; exact ⟨.inr k,hk⟩
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib,Pairing.stepSupport]
      rw [used_old_iff hp hinj,hp.boundary_used_iff hinj]

omit [Std.Symm r] in
lemma output_edge (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n)
    (hi : p.stepSupport a b t i) :
    full (r:=r) (old:=old) (p:=p) a b t (core (boundary old a b i)) (.inr (.inr i)) := by
  by_cases hia : i=a
  · subst i
    rw [boundary_left]
    exact Or.inl ⟨rfl,rfl,by simpa [Pairing.stepSupport] using hi⟩
  · by_cases hib : i=b
    · subst i
      simp only [Pairing.stepSupport,ite_eq_right hia,ite_true,eq_self] at hi
      simpa only [boundary_right old a b hab,core,full,Patch.glued,gateWiring] using
        (Or.inr ⟨rfl,rfl,hi⟩ : (b=a ∧ (3:Fin 4)=2 ∧ t.Occupied 2) ∨ (b=b ∧ (3:Fin 4)=3 ∧ t.Occupied 3))
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib,core,full,Patch.glued]
      exact ⟨i,by simpa [Pairing.stepSupport,hia,hib] using hi,rfl,by simp [gateInput,hia,hib]⟩

omit [Std.Symm r] in
lemma full_used_out (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n)
    (h : Graph.Used (full (r:=r) (old:=old) (p:=p) a b t) (.inr (.inr i))) :
    p.stepSupport a b t i := by
  obtain ⟨v,hv⟩ := h
  rcases v with v | (k | j)
  · obtain ⟨j,hj,he,_⟩ := hv
    obtain ⟨rfl,hja,hjb⟩ := (gateInput_eq_out a b j i).mp he.symm
    simpa [Pairing.stepSupport,hja,hjb] using hj
  · rcases hv with ⟨rfl,_,ht⟩ | ⟨rfl,_,ht⟩
    · simpa [Pairing.stepSupport] using ht
    · simpa [Pairing.stepSupport,hab.symm] using ht
  · exact hv.elim

omit [Std.Symm r] in
lemma project_used (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (v : Sum V (GateExterior n))
    (h : Graph.Used (full (r:=r) (old:=old) (p:=p) a b t) v) :
    Graph.Used (wiring r old p.Occupied a b t) (project old a b v) := by
  rcases v with v | (k | i)
  · apply (used_old_iff hp hinj a b t v).mpr
    obtain ⟨w,hw⟩ := h
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr w =>
      obtain ⟨i,hi,rfl,_⟩ := hw
      exact (hp.boundary_used_iff hinj i).mpr hi
  · obtain ⟨w,hw⟩ := h
    rcases w with w | (l | j)
    · obtain ⟨i,hi,he,rfl⟩ := hw
      rcases (gateInput_eq_box a b i hab k).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨.inl (old i),Or.inl ⟨rfl,rfl,hi⟩⟩
      · exact ⟨.inl (old i),Or.inr ⟨rfl,rfl,hi⟩⟩
    · exact ⟨.inr l,hw⟩
    · rcases hw with ⟨_,rfl,ht⟩ | ⟨_,rfl,ht⟩ <;>
        obtain ⟨l,hl⟩ := ht <;> exact ⟨.inr l,hl⟩
  · exact (used_output_iff hp hinj a b hab t i).mpr (full_used_out a b hab t i h)

 def contraction (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.WireContraction (full (r:=r) (old:=old) (p:=p) a b t)
      (wiring r old p.Occupied a b t) (fun i => .inr (.inr i)) (boundary old a b) where
  project := project old a b
  core := core
  section_eq := project_core old a b
  map_edge := project_edge a b hab t
  core_edge := core_edge a b hab t
  map_boundary := fun _ => rfl
  boundary_injective := boundary_injective old hinj a b
  map_used := project_used hp hinj a b hab t
  retract := by
    intro v hv
    rcases v with v | (k | i)
    · exact .refl
    · exact .refl
    · exact .single (symm (output_edge a b hab t i (full_used_out a b hab t i hv)))
  boundary_retract := fun i hi => .single (output_edge a b hab t i
    ((used_output_iff hp hinj a b hab t i).mp hi))

 theorem realizes_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (q : Pairing n) :
    GraphRealizes (full (r:=r) (old:=old) (p:=p) a b t) (fun i => .inr (.inr i)) q ↔
      GraphRealizes (wiring r old p.Occupied a b t) (boundary old a b) q :=
  (contraction hp hinj a b hab t).realizes_iff

end CompactGate
end LocalContractions

namespace Graph
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  [Std.Symm r] [Std.Symm s] {a : Fin n → V} {b : Fin n → W}

lemma used_of_reach {v w : V} (h : Relation.ReflTransGen r v w) (hv : Used r v) : Used r w := by
  by_cases he : v=w
  · exact he ▸ hv
  · exact used_of_reach_ne (symm h) (Ne.symm he)

omit [Std.Symm r] [Std.Symm s] in
lemma WireContraction.drains (e : WireContraction r s a b) (h : DrainsBoundary r a) :
    DrainsBoundary s b := by
  intro v w hvw
  obtain ⟨i,hr⟩ := h (e.core v) (e.core w) (e.core_edge v w hvw)
  have hm := Graph.map_reach e.project e.map_edge hr
  rw [e.section_eq,e.map_boundary] at hm
  exact ⟨i,hm⟩

omit [Std.Symm r] in
lemma WireContraction.drains_inv (e : WireContraction r s a b) (h : DrainsBoundary s b) :
    DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨x,hx⟩ := e.map_used v ⟨w,hvw⟩
  obtain ⟨i,hr⟩ := h (e.project v) x hx
  have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) hr
  exact ⟨i,((e.retract v ⟨w,hvw⟩).trans hm).trans
    (e.boundary_retract i (used_of_reach hr ⟨x,hx⟩))⟩

omit [Std.Symm r] in
lemma WireContraction.drains_iff (e : WireContraction r s a b) :
    DrainsBoundary r a ↔ DrainsBoundary s b := ⟨e.drains,e.drains_inv⟩

end Graph

 

 

open scoped Classical

namespace CompactGate
variable {V : Type*} {n : ℕ} (r : V → V → Prop) (old : Fin n → V)
  (active : Fin n → Prop) (a b : Fin n) (t : Tile)

def localEnd (v : V) : Sum V (Fin 4) → Prop
  | .inl w => Relation.ReflTransGen r v w
  | .inr _ => False

lemma reach_exit (v : V) {z : Sum V (Fin 4)}
    (hr : Relation.ReflTransGen (wiring r old active a b t) (.inl v) z) :
    (∃ i, Relation.ReflTransGen r v (old i)) ∨
      localEnd r v z := by
  induction hr with
  | refl => exact Or.inr .refl
  | @tail x y h hxy ih =>
    rcases ih with hi | hi
    · exact Or.inl hi
    · cases x with
      | inr k => exact hi.elim
      | inl w =>
        cases y with
        | inl u => exact Or.inr (hi.tail hxy)
        | inr k =>
          rcases hxy with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩
          · exact Or.inl ⟨a,hi⟩
          · exact Or.inl ⟨b,hi⟩

lemma drains_local (hd : Graph.DrainsBoundary (wiring r old active a b t) (boundary old a b)) :
    Graph.DrainsBoundary r old := by
  intro v w hvw
  obtain ⟨i,hi⟩ := hd (.inl v) (.inl w) hvw
  have he := reach_exit r old active a b t v hi
  rcases he with he | he
  · exact he
  · by_cases hia : i=a
    · simp only [boundary,ite_eq_left hia,localEnd] at he
    · by_cases hib : i=b
      · simp only [boundary,ite_eq_right hia,ite_eq_left hib,localEnd] at he
      · exact ⟨i,by simpa only [boundary,ite_eq_right hia,ite_eq_right hib,localEnd] using he⟩

end CompactGate

namespace Circuit
variable {n : ℕ}

def CompactVertex : Circuit n → Type
  | .nil => Fin n
  | .snoc c _ => Sum c.CompactVertex (Fin 4)

def compactBoundary : (c : Circuit n) → Fin n → c.CompactVertex
  | .nil => id
  | .snoc c g => CompactGate.boundary c.compactBoundary g.left g.right

def compactWiring (p : Pairing n) : (c : Circuit n) → c.CompactVertex → c.CompactVertex → Prop
  | .nil => p.Adj
  | .snoc c g => CompactGate.wiring (compactWiring p c) c.compactBoundary
      (support p c) g.left g.right g.tile

theorem compactBoundary_injective (c : Circuit n) : Function.Injective c.compactBoundary := by
  induction c with
  | nil => exact Function.injective_id
  | snoc c g ih => exact CompactGate.boundary_injective _ ih _ _

instance compactWiring_symm (p : Pairing n) (c : Circuit n) : Std.Symm (compactWiring p c) := by
  induction c with
  | nil => exact ⟨fun _ _ h => Pairing.adj_symm h⟩
  | snoc c g ih =>
    let := ih
    exact inferInstanceAs (Std.Symm (CompactGate.wiring _ _ _ _ _ _))

theorem compact_eval_sound (p : Pairing n) (c : Circuit n) (q : Pairing n)
    (h : eval p c=some q) : GraphRealizes (compactWiring p c) c.compactBoundary q := by
  induction c generalizing q with
  | nil => have he : p=q := Option.some.inj h; subst q; exact p.graphRealizes
  | snoc c g ih =>
    cases hr : eval p c with
    | none => simp [eval,hr] at h
    | some r =>
      have hstep : r.tileStep g.left g.right g.adjacent g.tile = some q := by
        simpa only [eval,hr,Option.bind_some] using h
      have hp := ih r hr
      have hs := (eval_sound p c r hr).2.2
      have hne : g.left≠g.right := by have := g.adjacent; intro hh; have := congrArg Fin.val hh; omega
      change GraphRealizes (CompactGate.wiring _ _ _ _ _ _) _ q
      rw [hs]
      exact (CompactGate.realizes_iff hp c.compactBoundary_injective g.left g.right hne g.tile q).mp
        ((graph_gate_step_iff hp g.left g.right g.adjacent g.tile q).mpr hstep).2

theorem compact_eval_exists (p : Pairing n) (c : Circuit n) (hc : Compatible p c)
    (hd : Graph.DrainsBoundary (compactWiring p c) c.compactBoundary) :
    ∃ q, eval p c=some q := by
  induction c with
  | nil => exact ⟨p,rfl⟩
  | snoc c g ih =>
    obtain ⟨hc,hl,hright⟩ := hc
    obtain ⟨r,hr⟩ := ih hc (CompactGate.drains_local
      (compactWiring p c) c.compactBoundary (support p c) g.left g.right g.tile hd)
    have hp := compact_eval_sound p c r hr
    have hs := (eval_sound p c r hr).2.2
    have hne : g.left≠g.right := by have := g.adjacent; intro hh; have := congrArg Fin.val hh; omega
    have hcomp : CutPatch.Compatible (r.cutShape g.left g.right) g.tile := by
      rw [r.cutShape_compatible]
      exact ⟨by simpa only [hs] using hl,by simpa only [hs] using hright⟩
    change Graph.DrainsBoundary (CompactGate.wiring _ _ _ _ _ _) _ at hd
    rw [hs] at hd
    have hfull := (CompactGate.contraction hp c.compactBoundary_injective g.left g.right hne g.tile).drains_inv hd
    obtain ⟨q,hq⟩ := graph_gate_step_exists hp g.left g.right g.adjacent g.tile hcomp hfull
    exact ⟨q,by simpa only [eval,hr,Option.bind_some] using hq⟩

theorem compact_eval_iff (p : Pairing n) (c : Circuit n) (q : Pairing n) :
    eval p c=some q ↔ Compatible p c ∧ GraphRealizes (compactWiring p c) c.compactBoundary q := by
  constructor
  · intro h; exact ⟨(eval_sound p c q h).1,compact_eval_sound p c q h⟩
  · rintro ⟨hc,hq⟩
    obtain ⟨r,hr⟩ := compact_eval_exists p c hc hq.drainsBoundary
    have he := (compact_eval_sound p c r hr).unique hq
    exact he ▸ hr

end Circuit
end
end CriticalStrip.Diagram

end OAI
