import Mathlib
import OAI.Geometry.HyperbolicGroups.PresentationDisk
import OAI.Geometry.HyperbolicGroups.GraphWordFilling

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

def adj : CoreGeometry.Vertex → CoreGeometry.Vertex → Prop
  | .inl r,.inr l => ∃ e : IncidenceTemplate.Edge, e.val = (r,l) ∧ e ∈ S
  | .inr l,.inl r => ∃ e : IncidenceTemplate.Edge, e.val = (r,l) ∧ e ∈ S
  | _,_ => False

def graph : SimpleGraph CoreGeometry.Vertex where
  Adj := adj S
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

lemma core_adj {a b : CoreGeometry.Vertex} (h : (graph S).Adj a b) :
    CoreGeometry.Adjacent a b := by
  cases a <;> cases b <;> try exact h.elim
  all_goals
    obtain ⟨e,he,hm⟩ := h
    have hh := e.property
    rw [he] at hh
    exact hh

lemma core_edge_mem {a b : CoreGeometry.Vertex} (h : (graph S).Adj a b) :
    MasterGraph.coreEdge (core_adj S h) ∈ S := by
  cases a <;> cases b <;> try exact h.elim
  all_goals
    have hold := h
    obtain ⟨e,he,hm⟩ := h
    have hh : MasterGraph.coreEdge (core_adj S hold) = e := Subtype.ext he.symm
    rwa [hh]

def projection : MasterGraph.Vertex → CoreGeometry.Vertex
  | .inl x => x
  | .inr _ => .inl 0

lemma oriented_adj {a b : MasterGraph.Vertex} (s : Step a b)
    (e : IncidenceTemplate.Edge) (he : s.field = .inl e) (hm : e ∈ S) :
    (graph S).Adj (projection a) (projection b) := by
  rcases s with ⟨f,o,hh⟩
  dsimp at he
  subst f
  cases o <;> simp only [Bool.false_eq_true,↓reduceIte,source,target] at hh
  all_goals rcases hh with ⟨rfl,rfl⟩; exact ⟨e,rfl,hm⟩

def label (n : ℕ) (l : Field → Alphabet n) (e : (graph S).Dart) : Alphabet n :=
  stepLetter n l (coreStep (core_adj S e.adj))

lemma label_rev (n : ℕ) (l : Field → Alphabet n) (e : (graph S).Dart) :
    label S n l e.symm = ((label S n l e).1,!(label S n l e).2) := by
  rcases e with ⟨⟨a,b⟩,h⟩
  cases a <;> cases b <;> try exact h.elim
  all_goals
    dsimp [label,SimpleGraph.Dart.symm,coreStep,stepLetter,Step.pos,Step.neg,inverseLetter] <;>
      simp only [Bool.not_not]

lemma oriented_label (n : ℕ) (l : Field → Alphabet n)
    {a b : MasterGraph.Vertex} (s : Step a b)
    (e : IncidenceTemplate.Edge) (he : s.field = .inl e) (hm : e ∈ S) :
    label S n l ⟨(projection a,projection b),oriented_adj S s e he hm⟩ = stepLetter n l s := by
  rcases s with ⟨f,o,hh⟩
  dsimp at he
  subst f
  cases o <;> simp only [Bool.false_eq_true,↓reduceIte,source,target] at hh
  all_goals rcases hh with ⟨rfl,rfl⟩; rfl

abbrev Fields {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) : Prop :=
  ∀ f ∈ p.fields, ∃ e : IncidenceTemplate.Edge, f = .inl e ∧ e ∈ S

def path {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    (graph S).Walk (projection a) (projection b) := by
  induction p with
  | nil a => exact .nil
  | cons s p ih =>
    let hh := hp _ List.mem_cons_self
    let e := Classical.choose hh
    exact .cons (oriented_adj S s e (Classical.choose_spec hh).1 (Classical.choose_spec hh).2) (ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)))

lemma path_length {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    (path S p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change (path S p (fun f hf => hp f (List.mem_cons_of_mem _ hf))).length + 1 = p.length + 1
    rw [ih]

lemma path_word (n : ℕ) (l : Field → Alphabet n)
    {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    GraphWordFilling.word (label S n l) (path S p hp) = pathWord n l p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    let hh := hp _ List.mem_cons_self
    let ht : Fields S p := fun f hf => hp f (List.mem_cons_of_mem _ hf)
    change label S n l ⟨_,oriented_adj S s (Classical.choose hh)
      (Classical.choose_spec hh).1 (Classical.choose_spec hh).2⟩ ::
      GraphWordFilling.word (label S n l) (path S p ht) = _ :: _
    rw [oriented_label S n l s (Classical.choose hh) (Classical.choose_spec hh).1 (Classical.choose_spec hh).2,ih]

def toMaster : {a b : CoreGeometry.Vertex} → (graph S).Walk a b → MasterGraph.Path (.inl a) (.inl b)
  | _,_,.nil => .nil _
  | _,_,.cons h p => .cons (coreStep (core_adj S h)) (toMaster p)

lemma toMaster_fields {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    Fields S (toMaster S p) := by
  induction p with
  | nil => simp [toMaster,Fields,Path.fields]
  | cons h p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨_,coreStep_field _,core_edge_mem S h⟩
    · exact ih f hf

lemma toMaster_word (n : ℕ) (l : Field → Alphabet n)
    {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    pathWord n l (toMaster S p) = GraphWordFilling.word (label S n l) p := by
  induction p with
  | nil => rfl
  | cons h p ih => change _ :: _ = _ :: _; exact congrArg (List.cons _) ih

lemma cycle_length {a : CoreGeometry.Vertex} (p : (graph S).Walk a a) (hp : p.IsCycle) :
    p.length ≤ 18 := by
  have h := hp.nodup_dropLast_support
  have hd := h.length_le_card
  have hl := p.length_support
  have hd' : p.support.dropLast.length ≤ 18 := by simpa using hd
  simpa using hd'

end HyperbolicObstruction.CoreWordGraph
end

end OAI
