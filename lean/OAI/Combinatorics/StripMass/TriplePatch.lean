import Mathlib
import OAI.Combinatorics.StripMass.ThreeBoxSplitPolynomial
import OAI.Combinatorics.StripMass.TripleCircuit

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def output (q : Pairing n) : Fin n ⊕ Fin n → Prop
  | .inl _ => False
  | .inr i => q.Occupied i

def reachTest (q : Pairing n) (r : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop) : Prop :=
  ∀ i j, r (.inr i) (.inr j) ↔ i=j ∨ q.Adj i j

def exteriorPredicate (p q : Pairing n) (k : Fin 51) : Prop :=
  s.Outside p q ∧ ThreeBox.exteriorTest (s.exterior p q) s.interface (s.active p q)
    (output q) (reachTest q) k

def patchEquiv (p q : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (s.attached p q t) (s.patch p q t) Sum.inr
      (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv exteriorEquiv (s.exterior_edge p q t) (fun _ => rfl)

lemma active_iff (p q : Pairing n) (t : ThreeBox.Config) :
    (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) ↔
      (p.Occupied s.a ↔ t.2.1.Occupied 0) ∧
      (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.c ↔ t.1.Occupied 1) ∧
      (q.Occupied s.a ↔ t.2.1.Occupied 2) ∧
      (q.Occupied s.b ↔ t.2.2.Occupied 2) ∧ (q.Occupied s.c ↔ t.2.2.Occupied 3) := by
  simp [Fin.forall_fin_succ,active,ThreeBox.boundaryOccupied,ThreeBox.boundary,
    ThreeBox.atRow,ThreeBox.row,ThreeBox.port]

lemma compatible_support_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.rightCircuit t) ∧ (∀ i, q.Occupied i ↔ s.support p t i) ↔
      s.Outside p q ∧ ThreeBox.Compatible t ∧
        (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) := by
  rw [s.compatible_iff,s.active_iff]
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  constructor
  · rintro ⟨⟨hc,ha,hb,hc'⟩,hs⟩
    refine ⟨?_,hc,ha,hb,hc',?_,?_,?_⟩
    · intro i hia hib hic
      simpa only [support,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (hs i).symm
    · simpa [support] using hs s.a
    · simpa [support,hab.symm] using hs s.b
    · simpa [support,hac.symm,hbc.symm] using hs s.c
  · rintro ⟨ho,hc,ha,hb,hc',hqa,hqb,hqc⟩
    refine ⟨⟨hc,ha,hb,hc'⟩,?_⟩
    intro i
    by_cases hia : i=s.a
    · subst i; simpa [support] using hqa
    · by_cases hib : i=s.b
      · subst i; simpa [support,hia] using hqb
      · by_cases hic : i=s.c
        · subst i; simpa [support,hia,hib] using hqc
        · simpa only [support,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (ho i hia hib hic).symm

lemma patchTest_realizes (p q : Pairing n) (t : ThreeBox.Config) :
    ThreeBox.patchTest (s.exterior p q) s.interface (s.active p q) (output q) (reachTest q) t ↔
      ThreeBox.Compatible t ∧ (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) ∧
        GraphRealizes (s.patch p q t) (fun i => .inr (.inr i)) q := by
  unfold ThreeBox.patchTest
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨hd,hr⟩
    refine ⟨?_,hr⟩
    intro v w he
    obtain ⟨(x|(i|i)),hi,h⟩ := hd v w he
    · exact hi.elim
    · exact hi.elim
    · exact ⟨i,hi,h⟩
  · intro h
    refine ⟨?_,h.reach⟩
    intro v w he
    obtain ⟨i,hi,hr⟩ := h.no_loop v w he
    exact ⟨.inr (.inr i),hi,hr⟩

lemma eval_patch_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      s.Outside p q ∧ ThreeBox.patchTest (s.exterior p q) s.interface (s.active p q)
        (output q) (reachTest q) t := by
  rw [s.eval_iff,s.patchTest_realizes]
  constructor
  · rintro ⟨hc,hr⟩
    have hs : ∀ i, q.Occupied i ↔ s.support p t i := fun i =>
      (hr.boundary_used_iff s.boundary_injective i).symm.trans (s.boundary_used p t i)
    obtain ⟨ho,hc',ha⟩ := (s.compatible_support_iff p q t).mp ⟨hc,hs⟩
    refine ⟨ho,hc',ha,?_⟩
    apply (s.patchEquiv p q t).realizes_iff.mp
    exact (Graph.Attached.contraction (s.wiring p t) s.boundary q.Occupied
      (fun i => (hs i).trans (s.boundary_used p t i).symm) s.boundary_injective).realizes_inv hr
  · rintro ⟨ho,hc,ha,hr⟩
    obtain ⟨hc',hs⟩ := (s.compatible_support_iff p q t).mpr ⟨ho,hc,ha⟩
    refine ⟨hc',?_⟩
    apply (Graph.Attached.contraction (s.wiring p t) s.boundary q.Occupied
      (fun i => (hs i).trans (s.boundary_used p t i).symm) s.boundary_injective).realizes
    exact (s.patchEquiv p q t).realizes_iff.mpr hr

lemma eval_profile_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      ∃ k, ThreeBox.profile t=some k ∧ s.exteriorPredicate p q k := by
  rw [s.eval_patch_iff,ThreeBox.patchTest_iff]
  unfold exteriorPredicate
  constructor
  · rintro ⟨ho,k,hk,hp⟩; exact ⟨k,hk,ho,hp⟩
  · rintro ⟨k,hk,ho,hp⟩; exact ⟨ho,k,hk,hp⟩

end TriplePosition

 

 

namespace Tile

def mirrorPort : Fin 4 → Fin 4 := ![1,0,3,2]
lemma mirrorPort_involutive : Function.Involutive mirrorPort := by intro i; fin_cases i <;> rfl

def mirrorPortEquiv : Fin 4 ≃ Fin 4 :=
  ⟨mirrorPort,mirrorPort,mirrorPort_involutive,mirrorPort_involutive⟩

def mirror : Tile → Tile
  | .vacant => .vacant
  | .vertical₀ => .vertical₁
  | .vertical₁ => .vertical₀
  | .diagonal₀ => .diagonal₁
  | .diagonal₁ => .diagonal₀
  | .cap => .cap
  | .cup => .cup
  | .verticalPair => .verticalPair
  | .capCup => .capCup

lemma mirror_involutive : Function.Involutive mirror := by intro t; cases t <;> rfl

def mirrorEquiv : Tile ≃ Tile := ⟨mirror,mirror,mirror_involutive,mirror_involutive⟩

lemma mirror_adj (t : Tile) (i j : Fin 4) :
    t.mirror.Adj i j ↔ t.Adj (mirrorPort i) (mirrorPort j) := by
  revert t i j
  decide

lemma mirror_occupied (t : Tile) (i : Fin 4) :
    t.mirror.Occupied i ↔ t.Occupied (mirrorPort i) := by
  unfold Occupied
  simp only [mirror_adj]
  exact mirrorPortEquiv.surjective.exists.symm

lemma weight_mirror {K : Type*} [One K] (w : Weights K) (t : Tile) :
    w.tile t.mirror=w.tile t := by cases t <;> rfl

end Tile

 

 

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def leftCircuit (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (s.left.gate t.1.mirror)) (s.right.gate t.2.1.mirror))
    (s.left.gate t.2.2.mirror)

def mirrorVertexEquiv : (((Fin n ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4) ≃ (Fin n ⊕ Fin 12) :=
  (Equiv.sumCongr (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) Tile.mirrorPortEquiv)
    Tile.mirrorPortEquiv) Tile.mirrorPortEquiv).trans vertexEquiv

def mirrorWiring (p : Pairing n) (t : ThreeBox.Config) : (Fin n ⊕ Fin 12) → (Fin n ⊕ Fin 12) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inr v,.inr w => ThreeBox.Adj t v w
  | .inl i,.inr v | .inr v,.inl i =>
      (i=s.c ∧ v=4 ∧ p.Occupied s.c) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨
      (i=s.a ∧ v=1 ∧ p.Occupied s.a)

def mirrorBoundary (i : Fin n) : Fin n ⊕ Fin 12 :=
  if i=s.c then .inr 6 else if i=s.b then .inr 10 else if i=s.a then .inr 11 else .inl i

@[simp] lemma mirror_vertex_old (i : Fin n) :
    mirrorVertexEquiv (.inl (.inl (.inl i)))=.inl i := rfl
@[simp] lemma mirror_vertex_zero (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inl (.inl (.inr i))))=
      .inr ⟨(Tile.mirrorPort i).val,by omega⟩ := rfl
@[simp] lemma mirror_vertex_one (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inl (.inr i)))=
      .inr ⟨4+(Tile.mirrorPort i).val,by omega⟩ := rfl
@[simp] lemma mirror_vertex_two (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inr i))=
      .inr ⟨4+(4+(Tile.mirrorPort i).val),by omega⟩ := rfl

lemma mirror_boundary_eq (t : ThreeBox.Config) (i : Fin n) :
    mirrorVertexEquiv ((s.leftCircuit t).compactBoundary i)=s.mirrorBoundary i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [leftCircuit, Circuit.compactBoundary, CompactGate.boundary, Position.gate, left,
      right, mirrorBoundary] <;> rfl

lemma mirror_edge_0_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_old]

lemma mirror_edge_0_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, mirrorWiring, mirror_vertex_old,
    mirror_vertex_zero, Tile.mirrorPort]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_0_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inr w))) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_0_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inr w)) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, mirrorWiring, mirror_vertex_old,
    mirror_vertex_zero, Tile.mirrorPort]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_zero, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_1_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_one, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_2_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_one, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_one, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_two, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_iff (p : Pairing n) (t : ThreeBox.Config)
    (v w : (s.leftCircuit t).CompactVertex) :
    Circuit.compactWiring p (s.leftCircuit t) v w ↔
      s.mirrorWiring p t (mirrorVertexEquiv v) (mirrorVertexEquiv w) := by
  rcases v with ((v|v)|v)|v <;> rcases w with ((w|w)|w)|w
  · exact s.mirror_edge_0_0 p t v w
  · exact s.mirror_edge_0_1 p t v w
  · exact s.mirror_edge_0_2 p t v w
  · exact s.mirror_edge_0_3 p t v w
  · exact s.mirror_edge_1_0 p t v w
  · exact s.mirror_edge_1_1 p t v w
  · exact s.mirror_edge_1_2 p t v w
  · exact s.mirror_edge_1_3 p t v w
  · exact s.mirror_edge_2_0 p t v w
  · exact s.mirror_edge_2_1 p t v w
  · exact s.mirror_edge_2_2 p t v w
  · exact s.mirror_edge_2_3 p t v w
  · exact s.mirror_edge_3_0 p t v w
  · exact s.mirror_edge_3_1 p t v w
  · exact s.mirror_edge_3_2 p t v w
  · exact s.mirror_edge_3_3 p t v w

def mirrorEquiv (p : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (Circuit.compactWiring p (s.leftCircuit t)) (s.mirrorWiring p t)
      (s.leftCircuit t).compactBoundary s.mirrorBoundary :=
  Graph.BoundaryEquiv.ofEquiv mirrorVertexEquiv (s.mirror_edge_iff p t) (s.mirror_boundary_eq t)


 

 

instance mirrorWiring_symm (p : Pairing n) (t : ThreeBox.Config) : Std.Symm (s.mirrorWiring p t) := by
  constructor
  rintro (i|v) (j|w) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · exact (ThreeBox.adj_symm t).symm _ _ h

lemma mirror_boundary_injective : Function.Injective s.mirrorBoundary := by
  let t : ThreeBox.Config := (.vacant,.vacant,.vacant)
  intro i j hij
  apply (s.leftCircuit t).compactBoundary_injective
  apply mirrorVertexEquiv.injective
  simpa only [s.mirror_boundary_eq] using hij

def mirrorSupport (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) : Prop :=
  if i=s.c then t.2.1.Occupied 2 else if i=s.b then t.2.2.Occupied 2
    else if i=s.a then t.2.2.Occupied 3 else p.Occupied i

lemma mirror_circuit_support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Circuit.support p (s.leftCircuit t) i ↔ s.mirrorSupport p t i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.c <;> by_cases hb : i=s.b <;> by_cases hc : i=s.a <;>
    simp_all [leftCircuit,Circuit.support,Position.gate,left,right,mirrorSupport,Tile.mirror_occupied,Tile.mirrorPort]

lemma mirror_boundary_used (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Graph.Used (s.mirrorWiring p t) (s.mirrorBoundary i) ↔ s.mirrorSupport p t i := by
  rw [←s.mirror_circuit_support p t i,←Circuit.compact_boundary_used]
  constructor
  · intro h
    have hh := (s.mirrorEquiv p t).inv_used _ h
    rwa [(s.mirrorEquiv p t).inv_boundary] at hh
  · intro h
    have hh := (s.mirrorEquiv p t).map_used _ h
    rwa [(s.mirrorEquiv p t).map_boundary] at hh

lemma mirror_compatible_iff (p : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.leftCircuit t) ↔
      ThreeBox.Compatible t ∧ (p.Occupied s.c ↔ t.2.1.Occupied 0) ∧
        (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.a ↔ t.1.Occupied 1) := by
  simp only [leftCircuit, Circuit.Compatible, Circuit.support, Position.gate, left, right, s.ab,
    s.bc, s.ac, s.ab.symm, s.bc.symm, s.ac.symm, ThreeBox.Compatible, true_and,
    Tile.mirror_occupied, Tile.mirrorPort, Matrix.cons_val_zero]
  itauto

lemma mirror_eval_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      Circuit.Compatible p (s.leftCircuit t) ∧ GraphRealizes (s.mirrorWiring p t) s.mirrorBoundary q := by
  rw [Circuit.compact_eval_iff,(s.mirrorEquiv p t).realizes_iff]

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
