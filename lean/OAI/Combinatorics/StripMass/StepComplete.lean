import Mathlib
import OAI.Combinatorics.StripMass.StepToCut

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace GraphRealizes

theorem boundary_used_iff {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (ha : Function.Injective a) (i : Fin n) :
    Graph.Used r (a i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨j,hj,hr⟩ := h.no_loop (a i) w hw
    rcases (h.reach i j).mp hr with hh | hh
    · exact hh ▸ hj
    · exact ⟨j,hh⟩
  · rintro ⟨j,hj⟩
    apply Graph.used_of_reach_ne ((h.reach i j).mpr (Or.inr hj))
    intro hh
    have he := ha hh
    subst j
    exact p.adj_irrefl i hj

end GraphRealizes

namespace Pairing

theorem tileStep_compatible {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) : CutPatch.Compatible (p.cutShape a b) t := by
  have hn : CutPatch.profile (p.cutShape a b) t ≠ none := by
    intro hh
    have := (p.tileStep_none_iff a b hab t).mpr hh
    rw [hq] at this
    cases this
  obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hn
  exact (CutPatch.realizes_of_profile hd).compatible

theorem cutGraph_profile_ne_none {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t) (q : Pairing n)
    (hq : GraphRealizes (p.cutGraph a b t) Sum.inr q) :
    CutPatch.profile (p.cutShape a b) t ≠ none := by
  intro hh
  obtain ⟨v,w,hvw,hout⟩ := CutPatch.none_has_closed hh hc
  obtain ⟨j,_,hr⟩ := hq.no_loop (.inl v) (.inl w) hvw
  obtain ⟨i,hi,hi',_⟩ := Patch.reach_to_exterior
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t) hr
  exact hout i hi hi'

theorem tileStep_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n) :
    p.tileStep a b hab t = some q ↔
      CutPatch.Compatible (p.cutShape a b) t ∧ GraphRealizes (p.stepWiring a b t) StepVertex.out q := by
  constructor
  · intro hq
    exact ⟨p.tileStep_compatible a b hab t q hq,p.stepWiring_realizes a b hab t q hq⟩
  · rintro ⟨hc,hq⟩
    have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
    have hg := (p.stepCutEquiv a b hne t).realizes hq
    have hn : p.tileStep a b hab t ≠ none := by
      intro hh
      exact p.cutGraph_profile_ne_none a b t hc q hg ((p.tileStep_none_iff a b hab t).mp hh)
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    have he := (p.stepWiring_realizes a b hab t r hr).unique hq
    exact he ▸ hr

theorem stepWiring_out_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) (i : Fin n) :
    Graph.Used (p.stepWiring a b t) (.out i) ↔
      (i=a ∧ t.Occupied 2) ∨ (i=b ∧ t.Occupied 3) ∨
        (i≠a ∧ i≠b ∧ p.Occupied i) := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | old j =>
      obtain ⟨rfl,hja,hjb,hj⟩ := hw
      exact Or.inr (Or.inr ⟨hja,hjb,hj⟩)
    | box k =>
      rcases hw with ⟨hi,_,h⟩ | ⟨hi,_,h⟩
      · exact Or.inl ⟨hi,h⟩
      · exact Or.inr (Or.inl ⟨hi,h⟩)
    | out j => exact hw.elim
  · rintro (⟨h,ht⟩ | ⟨h,ht⟩ | ⟨hia,hib,hi⟩)
    · exact ⟨.box 2,Or.inl ⟨h,rfl,ht⟩⟩
    · exact ⟨.box 3,Or.inr ⟨h,rfl,ht⟩⟩
    · exact ⟨.old i,rfl,hia,hib,hi⟩

def stepSupport {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) (i : Fin n) : Prop :=
  if i=a then t.Occupied 2 else if i=b then t.Occupied 3 else p.Occupied i

theorem tileStep_support {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) (i : Fin n) :
    q.Occupied i ↔ p.stepSupport a b t i := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  rw [← (p.stepWiring_realizes a b hab t q hq).boundary_used_iff (fun _ _ h => StepVertex.out.inj h) i,
    p.stepWiring_out_used]
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [stepSupport]

end Pairing

 

 


namespace Graph

def BoundaryEquiv.ofEquiv {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} (e : V ≃ W)
    (hr : ∀ v w, r v w ↔ s (e v) (e w)) (ha : ∀ i, e (a i)=b i) :
    BoundaryEquiv r s a b where
  toFun := e
  invFun := e.symm
  map_edge := fun v w h => .single ((hr v w).mp h)
  inv_edge := fun v w h => .single ((hr (e.symm v) (e.symm w)).mpr (by simpa using h))
  map_boundary := ha
  inv_boundary := fun i => by rw [←ha i]; exact e.symm_apply_apply _
  map_used := fun v ⟨w,h⟩ => ⟨e w,(hr v w).mp h⟩
  inv_used := fun v ⟨w,h⟩ => ⟨e.symm w,(hr (e.symm v) (e.symm w)).mpr (by simpa using h)⟩
  retract := fun v _ => by rw [e.symm_apply_apply]
  inv_retract := fun v _ => by rw [e.apply_symm_apply]

end Graph

abbrev GateExterior (n : ℕ) := Sum (Fin 4) (Fin n)

def gateWiring {n : ℕ} (a b : Fin n) (t : Tile) : GateExterior n → GateExterior n → Prop
  | .inl k, .inl l => t.Adj k l
  | .inr _, .inr _ => False
  | .inl k, .inr i | .inr i, .inl k =>
      (i=a ∧ k=2 ∧ t.Occupied 2) ∨ (i=b ∧ k=3 ∧ t.Occupied 3)

def gateInput {n : ℕ} (a b : Fin n) (i : Fin n) : GateExterior n :=
  if i=a then .inl 0 else if i=b then .inl 1 else .inr i

def stepVertexEquiv (n : ℕ) : StepVertex n ≃ Sum (Fin n) (GateExterior n) where
  toFun
    | .old i => .inl i
    | .box k => .inr (.inl k)
    | .out i => .inr (.inr i)
  invFun
    | .inl i => .old i
    | .inr (.inl k) => .box k
    | .inr (.inr i) => .out i
  left_inv := fun v => by cases v <;> rfl
  right_inv := fun v => by rcases v with i | (k | i) <;> rfl

@[simp] theorem gateInput_eq_box {n : ℕ} (a b i : Fin n) (hab : a≠b) (k : Fin 4) :
    gateInput a b i = .inl k ↔ (i=a ∧ k=0) ∨ (i=b ∧ k=1) := by
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [gateInput,eq_comm]

@[simp] theorem gateInput_eq_out {n : ℕ} (a b i j : Fin n) :
    gateInput a b i = .inr j ↔ i=j ∧ i≠a ∧ i≠b := by
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [gateInput]

namespace Pairing

theorem stepWiring_glued {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : StepVertex n) : p.stepWiring a b t v w ↔
      Patch.glued p.Adj (gateWiring a b t) id (gateInput a b) p.Occupied
        (stepVertexEquiv n v) (stepVertexEquiv n w) := by
  cases v <;> cases w <;> simp only [stepVertexEquiv,Equiv.coe_fn_mk,stepWiring,
    Patch.glued,gateWiring,id_eq]
  · rename_i i k
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i i j
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i k i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i j i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]

def stepGluedEquiv {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.BoundaryEquiv (p.stepWiring a b t)
      (Patch.glued p.Adj (gateWiring a b t) id (gateInput a b) p.Occupied)
      StepVertex.out (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv (stepVertexEquiv n) (p.stepWiring_glued a b hab t) (fun _ => rfl)

end Pairing

 

theorem graph_gate_step_iff {V : Type*} {n : ℕ} {r : V → V → Prop} {boundary : Fin n → V}
    {p : Pairing n} (hp : GraphRealizes r boundary p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n) :
    (CutPatch.Compatible (p.cutShape a b) t ∧
      GraphRealizes (Patch.glued r (gateWiring a b t) boundary (gateInput a b) p.Occupied)
        (fun i => .inr (.inr i)) q) ↔ p.tileStep a b hab t = some q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  rw [hp.substitute_iff,← (p.stepGluedEquiv a b hne t).realizes_iff,← p.tileStep_iff]


 

 


namespace Graph

def DrainsBoundary {V I : Type*} (r : V → V → Prop) (a : I → V) : Prop :=
  ∀ v w, r v w → ∃ i, Relation.ReflTransGen r v (a i)

theorem BoundaryEquiv.drains {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} (e : BoundaryEquiv r s a b)
    (h : DrainsBoundary r a) : DrainsBoundary s b := by
  intro v w hvw
  obtain ⟨x,hx⟩ := e.inv_used v ⟨w,hvw⟩
  obtain ⟨i,hi⟩ := h (e.invFun v) x hx
  refine ⟨i,?_⟩
  have hmap := Graph.map_reach e.toFun e.map_edge hi
  rw [e.map_boundary] at hmap
  exact (e.inv_retract v ⟨w,hvw⟩).trans hmap

theorem BoundaryEquiv.drains_iff {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} (e : BoundaryEquiv r s a b) :
    DrainsBoundary r a ↔ DrainsBoundary s b := ⟨e.drains,e.symm.drains⟩

theorem drains_glued_exterior_iff {V W I J : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (c : J → W) :
    DrainsBoundary (Patch.glued r s a b active) (fun i => .inr (c i)) ↔
      Patch.drains (Patch.glued r s a b active) (Patch.exteriorOutput (fun x => ∃ i, x=c i)) := by
  constructor
  · intro h v w hvw
    obtain ⟨i,hi⟩ := h v w hvw
    exact ⟨.inr (c i),⟨i,rfl⟩,hi⟩
  · intro h v w hvw
    obtain ⟨x,hx,hr⟩ := h v w hvw
    cases x with
    | inl x => exact hx.elim
    | inr x => obtain ⟨i,rfl⟩ := hx; exact ⟨i,hr⟩

theorem glued_drains_local {V W I J : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (c : J → W)
    (h : DrainsBoundary (Patch.glued r s a b active) (fun i => .inr (c i))) :
    DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨j,hj⟩ := h (.inl v) (.inl w) hvw
  obtain ⟨i,_,hi,_⟩ := Patch.reach_to_exterior r s a b active hj
  exact ⟨i,hi⟩

end Graph

namespace GraphRealizes

theorem drainsBoundary {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) : Graph.DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨i,_,hi⟩ := h.no_loop v w hvw
  exact ⟨i,hi⟩

theorem substitute_drains_iff {V B : Type*} {n m : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B) (c : Fin m → B) :
    Graph.DrainsBoundary (Patch.glued r s a b p.Occupied) (fun i => .inr (c i)) ↔
      Graph.DrainsBoundary (Patch.glued p.Adj s id b p.Occupied) (fun i => .inr (c i)) := by
  rw [Graph.drains_glued_exterior_iff,Graph.drains_glued_exterior_iff,h.drains_glued_iff]

end GraphRealizes

namespace Pairing

theorem tileStep_ne_none_of_drains {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t)
    (hd : Graph.DrainsBoundary (p.stepWiring a b t) StepVertex.out) :
    p.tileStep a b hab t ≠ none := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hg := (p.stepCutEquiv a b hne t).drains hd
  intro hh
  have hp := (p.tileStep_none_iff a b hab t).mp hh
  obtain ⟨v,w,hvw,hout⟩ := CutPatch.none_has_closed hp hc
  obtain ⟨j,hr⟩ := hg (.inl v) (.inl w) hvw
  obtain ⟨i,hi,hi',_⟩ := Patch.reach_to_exterior
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t) hr
  exact hout i hi hi'

end Pairing

theorem graph_gate_step_exists {V : Type*} {n : ℕ} {r : V → V → Prop} {boundary : Fin n → V}
    {p : Pairing n} (hp : GraphRealizes r boundary p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t)
    (hd : Graph.DrainsBoundary
      (Patch.glued r (gateWiring a b t) boundary (gateInput a b) p.Occupied)
      (fun i => .inr (.inr i))) : ∃ q, p.tileStep a b hab t = some q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hd' := (hp.substitute_drains_iff (gateWiring a b t) (gateInput a b) Sum.inr).mp hd
  have hd'' := (p.stepGluedEquiv a b hne t).symm.drains hd'
  exact Option.ne_none_iff_exists'.mp (p.tileStep_ne_none_of_drains a b hab t hc hd'')


 

 


structure Gate (n : ℕ) where
  left : Fin n
  right : Fin n
  adjacent : left.val+1=right.val
  tile : Tile

inductive Circuit (n : ℕ) where
  | nil : Circuit n
  | snoc : Circuit n → Gate n → Circuit n

namespace Circuit
variable {n : ℕ}

def Vertex : Circuit n → Type
  | .nil => Fin n
  | .snoc c _ => Sum c.Vertex (GateExterior n)

def boundary : (c : Circuit n) → Fin n → c.Vertex
  | .nil => id
  | .snoc _ _ => fun i => .inr (.inr i)

def support (p : Pairing n) : Circuit n → Fin n → Prop
  | .nil => p.Occupied
  | .snoc c g => fun i => if i=g.left then g.tile.Occupied 2
      else if i=g.right then g.tile.Occupied 3 else support p c i

def wiring (p : Pairing n) : (c : Circuit n) → c.Vertex → c.Vertex → Prop
  | .nil => p.Adj
  | .snoc c g => Patch.glued (wiring p c) (gateWiring g.left g.right g.tile)
      c.boundary (gateInput g.left g.right) (support p c)

def Compatible (p : Pairing n) : Circuit n → Prop
  | .nil => True
  | .snoc c g => Compatible p c ∧
      (support p c g.left ↔ g.tile.Occupied 0) ∧
      (support p c g.right ↔ g.tile.Occupied 1)

def eval (p : Pairing n) : Circuit n → Option (Pairing n)
  | .nil => some p
  | .snoc c g => (eval p c).bind (fun q => q.tileStep g.left g.right g.adjacent g.tile)

theorem eval_sound (p : Pairing n) (c : Circuit n) (q : Pairing n)
    (h : eval p c = some q) :
    Compatible p c ∧ GraphRealizes (wiring p c) c.boundary q ∧ support p c=q.Occupied := by
  induction c generalizing q with
  | nil =>
    have he : p=q := Option.some.inj h
    subst q
    exact ⟨trivial,p.graphRealizes,rfl⟩
  | snoc c g ih =>
    cases hp : eval p c with
    | none => simp [eval,hp] at h
    | some r =>
      have hstep : r.tileStep g.left g.right g.adjacent g.tile = some q := by
        simpa only [eval,hp,Option.bind_some] using h
      obtain ⟨hc,hr,hs⟩ := ih r hp
      have hsc := r.tileStep_compatible g.left g.right g.adjacent g.tile q hstep
      have hsc' := (r.cutShape_compatible g.left g.right g.tile).mp hsc
      refine ⟨⟨hc,?_,?_⟩,?_,?_⟩
      · simpa only [hs] using hsc'.1
      · simpa only [hs] using hsc'.2
      · change GraphRealizes (Patch.glued (wiring p c) (gateWiring g.left g.right g.tile)
          c.boundary (gateInput g.left g.right) (support p c)) (fun i => .inr (.inr i)) q
        rw [hs]
        exact ((graph_gate_step_iff hr g.left g.right g.adjacent g.tile q).mpr hstep).2
      · funext i
        apply propext
        change (if i=g.left then g.tile.Occupied 2 else
          if i=g.right then g.tile.Occupied 3 else support p c i) ↔ q.Occupied i
        rw [hs]
        exact (r.tileStep_support g.left g.right g.adjacent g.tile q hstep i).symm

theorem eval_exists (p : Pairing n) (c : Circuit n) (hc : Compatible p c)
    (hd : Graph.DrainsBoundary (wiring p c) c.boundary) : ∃ q, eval p c = some q := by
  induction c with
  | nil => exact ⟨p,rfl⟩
  | snoc c g ih =>
    obtain ⟨hc,hleft,hright⟩ := hc
    obtain ⟨r,hr⟩ := ih hc (Graph.glued_drains_local (wiring p c)
      (gateWiring g.left g.right g.tile) c.boundary (gateInput g.left g.right)
      (support p c) Sum.inr hd)
    obtain ⟨_,hreal,hs⟩ := eval_sound p c r hr
    have hcomp : CutPatch.Compatible (r.cutShape g.left g.right) g.tile := by
      rw [r.cutShape_compatible]
      exact ⟨by simpa only [hs] using hleft,by simpa only [hs] using hright⟩
    have hd' : Graph.DrainsBoundary (Patch.glued (wiring p c)
        (gateWiring g.left g.right g.tile) c.boundary (gateInput g.left g.right) r.Occupied)
        (fun i => .inr (.inr i)) := by
      change Graph.DrainsBoundary (Patch.glued (wiring p c)
        (gateWiring g.left g.right g.tile) c.boundary (gateInput g.left g.right) (support p c))
        (fun i => .inr (.inr i)) at hd
      rwa [hs] at hd
    obtain ⟨q,hq⟩ := graph_gate_step_exists hreal g.left g.right g.adjacent g.tile hcomp hd'
    exact ⟨q,by simpa only [eval,hr,Option.bind_some] using hq⟩

theorem eval_iff (p : Pairing n) (c : Circuit n) (q : Pairing n) :
    eval p c = some q ↔ Compatible p c ∧ GraphRealizes (wiring p c) c.boundary q := by
  constructor
  · intro h
    exact ⟨(eval_sound p c q h).1,(eval_sound p c q h).2.1⟩
  · rintro ⟨hc,hq⟩
    obtain ⟨r,hr⟩ := eval_exists p c hc hq.drainsBoundary
    have he := (eval_sound p c r hr).2.1.unique hq
    exact he ▸ hr

end Circuit
end

 

 

noncomputable section
open Finset
open scoped Classical

structure Position (n : ℕ) where
  left : Fin n
  right : Fin n
  adjacent : left.val+1=right.val

def Position.gate {n : ℕ} (a : Position n) (t : Tile) : Gate n :=
  ⟨a.left,a.right,a.adjacent,t⟩

def optionMatrix {K P Q : Type*} [Zero K] [One K] (f : P → Option Q) : Matrix Q P K :=
  fun q p => if f p=some q then 1 else 0

theorem optionMatrix_mul {K P Q R : Type*} [Semiring K] [Fintype Q]
    (f : P → Option Q) (g : Q → Option R) :
    (optionMatrix g : Matrix R Q K) * (optionMatrix f : Matrix Q P K) = optionMatrix (fun p => (f p).bind g) := by
  ext r p
  simp only [Matrix.mul_apply,optionMatrix]
  rcases Option.eq_none_or_eq_some (f p) with he | ⟨q,he⟩
  · simp [he]
  · simp only [he,Option.bind_some]
    rw [sum_eq_single q]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

variable {K : Type*} [CommRing K]

def localR {n : ℕ} (a : Position n) (w : Weights K) : Matrix (Pairing n) (Pairing n) K :=
  ∑ t : Tile, w.tile t • optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t)

inductive Program (n : ℕ) (K : Type*) where
  | nil : Program n K
  | snoc : Program n K → Position n → Weights K → Program n K

namespace Program
variable {n : ℕ}

def Choices : Program n K → Type
  | .nil => PUnit
  | .snoc p _ _ => p.Choices × Tile

instance choicesFinite (p : Program n K) : Fintype p.Choices := by
  induction p with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | snoc p _ _ ih => letI := ih; exact inferInstanceAs (Fintype (p.Choices × Tile))

def circuit : (p : Program n K) → p.Choices → Circuit n
  | .nil,_ => .nil
  | .snoc p a _,(c,t) => .snoc (p.circuit c) (a.gate t)

def weight : (p : Program n K) → p.Choices → K
  | .nil,_ => 1
  | .snoc p _ w,(c,t) => p.weight c * w.tile t

def matrix : Program n K → Matrix (Pairing n) (Pairing n) K
  | .nil => 1
  | .snoc p a w => localR a w * p.matrix

lemma matrix_expansion (p : Program n K) : p.matrix =
    ∑ c : p.Choices, p.weight c • optionMatrix (fun q => Circuit.eval q (p.circuit c)) := by
  induction p with
  | nil =>
    change (1 : Matrix (Pairing n) (Pairing n) K) =
      ∑ _ : PUnit, (1:K) • optionMatrix (fun q : Pairing n => some q)
    rw [Fintype.sum_unique]
    ext q r
    simp [optionMatrix,Matrix.one_apply,eq_comm]
  | snoc p a w ih =>
    simp only [matrix,localR,ih,mul_sum,sum_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    change (∑ c : p.Choices, ∑ t : Tile,
        (p.weight c * w.tile t) • (optionMatrix (fun q : Pairing n => q.tileStep a.left a.right a.adjacent t) *
          optionMatrix (fun q => Circuit.eval q (p.circuit c)))) = _
    simp_rw [optionMatrix_mul]
    change _ = ∑ c : p.Choices × Tile, _
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro t _
    simp only [weight,circuit,Circuit.eval,Position.gate]

lemma matrix_apply (p : Program n K) (q r : Pairing n) : p.matrix q r =
    ∑ c : p.Choices, if Circuit.eval r (p.circuit c)=some q then p.weight c else 0 := by
  rw [matrix_expansion]
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix,smul_eq_mul,mul_ite,mul_one,mul_zero]

end Program
end
end CriticalStrip.Diagram

end OAI
