import Mathlib
import OAI.Combinatorics.StripMass.WireContraction

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

structure TriplePosition (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a.val+1=b.val
  hbc : b.val+1=c.val

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma ab : s.a≠s.b := by intro he; have:=congrArg Fin.val he; have:=s.hab; omega
lemma bc : s.b≠s.c := by intro he; have:=congrArg Fin.val he; have:=s.hbc; omega
lemma ac : s.a≠s.c := by intro he; have:=congrArg Fin.val he; have:=s.hab; have:=s.hbc; omega

def left : Position n := ⟨s.a,s.b,s.hab⟩
def right : Position n := ⟨s.b,s.c,s.hbc⟩

def rightCircuit (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (s.right.gate t.1)) (s.left.gate t.2.1)) (s.right.gate t.2.2)

def vertexEquiv : (((Fin n ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4) ≃ (Fin n ⊕ Fin 12) :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)).trans
      (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)))

def wiring (p : Pairing n) (t : ThreeBox.Config) : (Fin n ⊕ Fin 12) → (Fin n ⊕ Fin 12) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inr v,.inr w => ThreeBox.Adj t v w
  | .inl i,.inr v | .inr v,.inl i =>
      (i=s.a ∧ v=4 ∧ p.Occupied s.a) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨
      (i=s.c ∧ v=1 ∧ p.Occupied s.c)

def boundary (i : Fin n) : Fin n ⊕ Fin 12 :=
  if i=s.a then .inr 6 else if i=s.b then .inr 10 else if i=s.c then .inr 11 else .inl i

@[simp] lemma vertex_old (i : Fin n) : vertexEquiv (.inl (.inl (.inl i)))=.inl i := rfl
@[simp] lemma vertex_zero (i : Fin 4) : (vertexEquiv (n:=n) (.inl (.inl (.inr i))))=
    .inr ⟨i.val,by omega⟩ := rfl
@[simp] lemma vertex_one (i : Fin 4) : (vertexEquiv (n:=n) (.inl (.inr i)))=
    .inr ⟨4+i.val,by omega⟩ := rfl
@[simp] lemma vertex_two (i : Fin 4) : (vertexEquiv (n:=n) (.inr i))=
    .inr ⟨4+(4+i.val),by omega⟩ := rfl

lemma boundary_eq (t : ThreeBox.Config) (i : Fin n) :
    vertexEquiv ((s.rightCircuit t).compactBoundary i) = s.boundary i := by
  have hab := s.ab; have hbc := s.bc; have hac := s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [rightCircuit, Circuit.compactBoundary, CompactGate.boundary, Position.gate, left,
      right, boundary] <;> rfl

lemma edge_0_0 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_old]

lemma edge_0_1 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, wiring, vertex_old, vertex_zero]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_0_2 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inr w))) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_one, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_0_3 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inr w)) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_two, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, wiring, vertex_old, vertex_zero]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_zero, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_1_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_one, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_2_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_one,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_two, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_one,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_iff (p : Pairing n) (t : ThreeBox.Config)
    (v w : (s.rightCircuit t).CompactVertex) :
    Circuit.compactWiring p (s.rightCircuit t) v w ↔ s.wiring p t (vertexEquiv v) (vertexEquiv w) := by
  rcases v with ((i|v)|v)|v <;> rcases w with ((j|w)|w)|w
  · exact s.edge_0_0 p t _ _
  · exact s.edge_0_1 p t _ _
  · exact s.edge_0_2 p t _ _
  · exact s.edge_0_3 p t _ _
  · exact s.edge_1_0 p t _ _
  · exact s.edge_1_1 p t _ _
  · exact s.edge_1_2 p t _ _
  · exact s.edge_1_3 p t _ _
  · exact s.edge_2_0 p t _ _
  · exact s.edge_2_1 p t _ _
  · exact s.edge_2_2 p t _ _
  · exact s.edge_2_3 p t _ _
  · exact s.edge_3_0 p t _ _
  · exact s.edge_3_1 p t _ _
  · exact s.edge_3_2 p t _ _
  · exact s.edge_3_3 p t _ _

end TriplePosition

 

 

namespace CompactGate
variable {V : Type*} {n : ℕ} (r : V → V → Prop) (old : Fin n → V)
  (active : Fin n → Prop) (a b : Fin n) (t : Tile)

lemma output_used (k : Fin 4) (hk0 : k≠0) (hk1 : k≠1) :
    Graph.Used (wiring r old active a b t) (.inr k) ↔ t.Occupied k := by
  constructor
  · rintro ⟨(v|l),h⟩
    · exact h.elim (fun h => (hk0 h.2.1).elim) (fun h => (hk1 h.2.1).elim)
    · exact ⟨l,h⟩
  · rintro ⟨l,h⟩; exact ⟨.inr l,h⟩

lemma passed_used (hinj : Function.Injective old) (i : Fin n) (hia : i≠a) (hib : i≠b) :
    Graph.Used (wiring r old active a b t) (.inl (old i)) ↔ Graph.Used r (old i) := by
  constructor
  · rintro ⟨(v|k),h⟩
    · exact ⟨v,h⟩
    · exact h.elim (fun h => (hia (hinj h.1)).elim) (fun h => (hib (hinj h.1)).elim)
  · rintro ⟨v,h⟩; exact ⟨.inl v,h⟩

lemma boundary_used (hinj : Function.Injective old) (_hab : a≠b)
    (ha : ∀ i, Graph.Used r (old i) ↔ active i) (i : Fin n) :
    Graph.Used (wiring r old active a b t) (boundary old a b i) ↔
      if i=a then t.Occupied 2 else if i=b then t.Occupied 3 else active i := by
  by_cases hia : i=a
  · subst i
    simp only [boundary]
    exact output_used r old active a b t 2 (by decide) (by decide)
  · by_cases hib : i=b
    · subst i
      simp only [boundary, ite_eq_right hia]
      exact output_used r old active a b t 3 (by decide) (by decide)
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib]
      exact (passed_used r old active a b t hinj i hia hib).trans (ha i)
end CompactGate

namespace Circuit
variable {n : ℕ}
lemma compact_boundary_used (p : Pairing n) (c : Circuit n) (i : Fin n) :
    Graph.Used (compactWiring p c) (c.compactBoundary i) ↔ support p c i := by
  induction c generalizing i with
  | nil => rfl
  | snoc c g ih =>
    have hne : g.left≠g.right := by intro he; have:=congrArg Fin.val he; have:=g.adjacent; omega
    exact CompactGate.boundary_used (compactWiring p c) c.compactBoundary (support p c)
      g.left g.right g.tile c.compactBoundary_injective hne ih i
end Circuit

 

 

namespace ThreeBox
instance adjStdSymm (t : Config) : Std.Symm (Adj t) := adj_symm t
end ThreeBox
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

instance wiring_symm (p : Pairing n) (t : ThreeBox.Config) : Std.Symm (s.wiring p t) := by
  constructor
  rintro (i|v) (j|w) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · exact (ThreeBox.adj_symm t).symm _ _ h

def equiv (p : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (Circuit.compactWiring p (s.rightCircuit t)) (s.wiring p t)
      (s.rightCircuit t).compactBoundary s.boundary :=
  Graph.BoundaryEquiv.ofEquiv vertexEquiv (s.edge_iff p t) (s.boundary_eq t)

lemma boundary_injective : Function.Injective s.boundary := by
  let t : ThreeBox.Config := (.vacant,.vacant,.vacant)
  intro i j hij
  apply (s.rightCircuit t).compactBoundary_injective
  apply vertexEquiv.injective
  simpa only [s.boundary_eq] using hij

def support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) : Prop :=
  if i=s.a then t.2.1.Occupied 2 else if i=s.b then t.2.2.Occupied 2
    else if i=s.c then t.2.2.Occupied 3 else p.Occupied i

lemma circuit_support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Circuit.support p (s.rightCircuit t) i ↔ s.support p t i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [rightCircuit,Circuit.support,Position.gate,left,right,support]

lemma boundary_used (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Graph.Used (s.wiring p t) (s.boundary i) ↔ s.support p t i := by
  rw [←s.circuit_support p t i,←Circuit.compact_boundary_used]
  constructor
  · intro h
    have hh := (s.equiv p t).inv_used _ h
    rwa [(s.equiv p t).inv_boundary] at hh
  · intro h
    have hh := (s.equiv p t).map_used _ h
    rwa [(s.equiv p t).map_boundary] at hh

lemma compatible_iff (p : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.rightCircuit t) ↔
      ThreeBox.Compatible t ∧ (p.Occupied s.a ↔ t.2.1.Occupied 0) ∧
        (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.c ↔ t.1.Occupied 1) := by
  simp only [rightCircuit, Circuit.Compatible, Circuit.support, Position.gate, left, right, s.ab,
    s.bc, s.ac, s.ab.symm, s.bc.symm, s.ac.symm, ThreeBox.Compatible, true_and]
  itauto

lemma eval_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      Circuit.Compatible p (s.rightCircuit t) ∧ GraphRealizes (s.wiring p t) s.boundary q := by
  rw [Circuit.compact_eval_iff,(s.equiv p t).realizes_iff]

end TriplePosition
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.Graph
noncomputable section
namespace Attached
variable {V : Type*} {n : ℕ}

def wiring (r : V → V → Prop) (old : Fin n → V) (active : Fin n → Prop) :
    (V ⊕ Fin n) → (V ⊕ Fin n) → Prop
  | .inl v,.inl w => r v w
  | .inl v,.inr i | .inr i,.inl v => v=old i ∧ active i
  | .inr _,.inr _ => False

def project (old : Fin n → V) : V ⊕ Fin n → V
  | .inl v => v
  | .inr i => old i

instance wiring_symm (r : V → V → Prop) [Std.Symm r] (old : Fin n → V) (active : Fin n → Prop) :
    Std.Symm (wiring r old active) := by
  constructor
  rintro (v|i) (w|j) h
  · change r v w at h; change r w v; exact symm h
  all_goals exact h

variable (r : V → V → Prop) (old : Fin n → V) (active : Fin n → Prop)
  (ha : ∀ i, active i ↔ Used r (old i))

include ha in
lemma map_used (v : V ⊕ Fin n) (h : Used (wiring r old active) v) : Used r (project old v) := by
  obtain ⟨w,hw⟩ := h
  rcases v with v | i <;> rcases w with w | j
  · exact ⟨w,hw⟩
  · obtain ⟨rfl,hj⟩ := hw; exact (ha j).mp hj
  · exact (ha i).mp hw.2
  · exact hw.elim

def contraction (hi : Function.Injective old) :
    WireContraction (wiring r old active) r Sum.inr old where
  project := project old
  core := Sum.inl
  section_eq := fun _ => rfl
  map_edge := by
    rintro (v|i) (w|j) h
    · exact .single h
    · rw [h.1]; exact .refl
    · rw [h.1]; exact .refl
    · exact h.elim
  core_edge := fun _ _ h => h
  map_boundary := fun _ => rfl
  boundary_injective := hi
  map_used := map_used r old active ha
  retract := by
    rintro (v|i) ⟨w,hw⟩
    · exact .refl
    · cases w with
      | inl w => exact .single ⟨rfl,hw.2⟩
      | inr j => exact hw.elim
  boundary_retract := fun i hu => .single ⟨rfl,(ha i).mpr hu⟩

end Attached
end
end CriticalStrip.Diagram.Graph

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def interface : Fin 6 → Fin n ⊕ Fin n :=
  ![.inl s.a,.inl s.b,.inl s.c,.inr s.a,.inr s.b,.inr s.c]

def active (p q : Pairing n) : Fin 6 → Prop :=
  ![p.Occupied s.a,p.Occupied s.b,p.Occupied s.c,
    q.Occupied s.a,q.Occupied s.b,q.Occupied s.c]

def exterior (p q : Pairing n) : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inl i,.inr j | .inr j,.inl i => i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c ∧ q.Occupied i
  | .inr _,.inr _ => False

def Outside (p q : Pairing n) : Prop :=
  ∀ i, i≠s.a → i≠s.b → i≠s.c → (p.Occupied i ↔ q.Occupied i)

def attached (p q : Pairing n) (t : ThreeBox.Config) :=
  Graph.Attached.wiring (s.wiring p t) s.boundary q.Occupied

def patch (p q : Pairing n) (t : ThreeBox.Config) :=
  Patch.glued (ThreeBox.Adj t) (s.exterior p q) ThreeBox.boundary s.interface (s.active p q)

def exteriorEquiv : ((Fin n ⊕ Fin 12) ⊕ Fin n) ≃ (Fin 12 ⊕ (Fin n ⊕ Fin n)) where
  toFun
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr v) => .inl v
    | .inr i => .inr (.inr i)
  invFun
    | .inl v => .inl (.inr v)
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inr i
  left_inv := by rintro ((i|v)|i) <;> rfl
  right_inv := by rintro (v|(i|i)) <;> rfl

lemma boundary_old (i j : Fin n) :
    ((.inl i : Fin n ⊕ Fin 12)=s.boundary j) ↔
      i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c := by
  by_cases ha : j=s.a <;> by_cases hb : j=s.b <;> by_cases hc : j=s.c <;>
    simp_all [boundary]

lemma boundary_new (v : Fin 12) (j : Fin n) :
    ((.inr v : Fin n ⊕ Fin 12)=s.boundary j) ↔
      (j=s.a ∧ v=6) ∨ (j=s.b ∧ v=10) ∨ (j=s.c ∧ v=11) := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : j=s.a <;> by_cases hb : j=s.b <;> by_cases hc : j=s.c <;>
    simp_all [boundary]

lemma interface_old (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.active p q k ∧ v=ThreeBox.boundary k ∧ (.inl i : Fin n ⊕ Fin n)=s.interface k) ↔
      (i=s.a ∧ v=4 ∧ p.Occupied s.a) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨ (i=s.c ∧ v=1 ∧ p.Occupied s.c) := by
  simp only [Fin.exists_fin_succ,interface,active,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inl.injEq,Sum.inl_ne_inr,and_false,or_false,Fin.exists_fin_zero]
  itauto

lemma interface_new (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.active p q k ∧ v=ThreeBox.boundary k ∧ (.inr i : Fin n ⊕ Fin n)=s.interface k) ↔
      ((i=s.a ∧ v=6) ∨ (i=s.b ∧ v=10) ∨ (i=s.c ∧ v=11)) ∧ q.Occupied i := by
  simp only [Fin.exists_fin_succ,interface,active,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inr.injEq,Sum.inr_ne_inl,and_false,false_or,or_false,Fin.exists_fin_zero]
  constructor
  · rintro (⟨h,hv,hi⟩ | ⟨h,hv,hi⟩ | ⟨h,hv,hi⟩) <;> subst i
    · exact ⟨Or.inl ⟨rfl,hv⟩,h⟩
    · exact ⟨Or.inr (Or.inl ⟨rfl,hv⟩),h⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl,hv⟩),h⟩
  · rintro ⟨(⟨rfl,hv⟩|⟨rfl,hv⟩|⟨rfl,hv⟩),h⟩
    · exact Or.inl ⟨h,hv,rfl⟩
    · exact Or.inr (Or.inl ⟨h,hv,rfl⟩)
    · exact Or.inr (Or.inr ⟨h,hv,rfl⟩)

lemma exterior_edge (p q : Pairing n) (t : ThreeBox.Config)
    (v w : (Fin n ⊕ Fin 12) ⊕ Fin n) :
    s.attached p q t v w ↔ s.patch p q t (exteriorEquiv v) (exteriorEquiv w) := by
  rcases v with (i|v)|i <;> rcases w with (j|w)|j
  all_goals dsimp only [attached,Graph.Attached.wiring,patch,Patch.glued,exteriorEquiv,Equiv.coe_fn_mk]
  · rfl
  · simpa only [wiring,and_comm,and_left_comm,and_assoc] using (s.interface_old p q w i).symm
  · rw [s.boundary_old]
    change ((i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c) ∧ q.Occupied j) ↔
      i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c ∧ q.Occupied i
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · exact (s.interface_old p q v j).symm
  · rfl
  · rw [s.boundary_new]
    exact (s.interface_new p q v j).symm
  · rw [s.boundary_old]
    change ((j=i ∧ j≠s.a ∧ j≠s.b ∧ j≠s.c) ∧ q.Occupied i) ↔
      j=i ∧ j≠s.a ∧ j≠s.b ∧ j≠s.c ∧ q.Occupied j
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · rw [s.boundary_new]
    simpa only [and_comm,and_left_comm,and_assoc] using (s.interface_new p q w i).symm
  · rfl

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
