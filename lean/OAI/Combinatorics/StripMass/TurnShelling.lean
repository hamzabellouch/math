import Mathlib
import OAI.Combinatorics.StripMass.TurnDisk

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Graph

 
lemma reach_before_sewing {V I : Type*} {r s : V → V → Prop} (b : I → V)
    (hs : ∀ v w,s v w → r v w ∨ ∃ i,v=b i) {v w : V}
    (h : Relation.ReflTransGen s v w) :
    (∃ i,Relation.ReflTransGen r v (b i)) ∨ Relation.ReflTransGen r v w := by
  induction h with
  | refl => exact Or.inr .refl
  | @tail y z h e ih =>
    rcases ih with h|h
    · exact Or.inl h
    · rcases hs _ _ e with he|⟨i,rfl⟩
      · exact Or.inr (h.tail he)
      · exact Or.inl ⟨i,h⟩

lemma drains_before_sewing {V I J : Type*} {r s : V → V → Prop}
    (b : I → V) (c : J → V)
    (hrs : ∀ v w,r v w → s v w)
    (hs : ∀ v w,s v w → r v w ∨ ∃ i,v=b i)
    (hc : ∀ j,∃ i,c j=b i) (hd : DrainsBoundary s c) : DrainsBoundary r b := by
  intro v w hvw
  obtain ⟨j,hj⟩:=hd v w (hrs _ _ hvw)
  rcases reach_before_sewing b hs hj with h|h
  · exact h
  · obtain ⟨i,hi⟩:=hc j
    exact ⟨i,hi ▸ h⟩

end Graph

namespace BoundaryInsert
lemma drains_old {V W : Type*} {n m : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    (a : Fin n → V) (b : Fin m → W) (k : ℕ) (hk : k≤n)
    (hd : Graph.DrainsBoundary (unionGraph r s) (boundary k hk a b)) :
    Graph.DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨i,hi⟩:=hd (.inl v) (.inl w) hvw
  obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
  · rw [boundary_old] at hi
    obtain ⟨x,hx,h⟩:=reach_left r s hi
    cases hx
    exact ⟨j,h⟩
  · rw [boundary_fresh] at hi
    obtain ⟨x,hx,_⟩:=reach_left r s hi
    cases hx
lemma drains_fresh {V W : Type*} {n m : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    (a : Fin n → V) (b : Fin m → W) (k : ℕ) (hk : k≤n)
    (hd : Graph.DrainsBoundary (unionGraph r s) (boundary k hk a b)) :
    Graph.DrainsBoundary s b := by
  intro v w hvw
  obtain ⟨i,hi⟩:=hd (.inr v) (.inr w) hvw
  obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
  · rw [boundary_old] at hi
    obtain ⟨x,hx,_⟩:=reach_right r s hi
    cases hx
  · rw [boundary_fresh] at hi
    obtain ⟨x,hx,h⟩:=reach_right r s hi
    cases hx
    exact ⟨j,h⟩

end BoundaryInsert

 

inductive TurnDisk : ℕ → Type
  | atom {n : ℕ} (p : Pairing n) (g : Fin n → ℤ) : TurnDisk n
  | insert {n m : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k≤n)
      (p : Pairing m) (g : Fin m → ℤ) : TurnDisk (n+m)
  | attach {n m : ℕ} (D : TurnDisk n) (E : TurnDisk m) (k : ℕ) (hk : k≤n) : TurnDisk (n+m)
  | sew {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n) : TurnDisk n

namespace TurnDisk

variable {boundarySize : ℕ}

def Vertex : {n : ℕ} → TurnDisk n → Type
  | n,.atom _ _ => Fin n
  | _,@TurnDisk.insert n m D _ _ _ _ => D.Vertex ⊕ Fin m
  | _,.attach D E _ _ => D.Vertex ⊕ E.Vertex
  | _,.sew D _ _ => D.Vertex

def boundary : {n : ℕ} → (D : TurnDisk n) → Fin n → D.Vertex
  | _,.atom _ _ => id
  | _,.insert D k hk _ _ => BoundaryInsert.boundary k hk D.boundary id
  | _,.attach D E k hk => BoundaryInsert.boundary k hk D.boundary E.boundary
  | _,.sew D k hk => D.boundary ∘ BoundaryErase.keep k hk

def gauge : {n : ℕ} → TurnDisk n → Fin n → ℤ
  | _,.atom _ g => g
  | _,.insert D k hk _ g => BoundaryInsert.gauge k hk D.gauge g
  | _,.attach D E k hk => BoundaryInsert.gauge k hk D.gauge E.gauge
  | _,.sew D k hk => D.gauge ∘ BoundaryErase.keep k hk

def wiring : {n : ℕ} → (D : TurnDisk n) → D.Vertex → D.Vertex → Prop
  | _,.atom p _ => p.Adj
  | _,.insert D _ _ p _ => BoundaryInsert.unionGraph D.wiring p.Adj
  | _,.attach D E _ _ => BoundaryInsert.unionGraph D.wiring E.wiring
  | _,.sew D k hk => BoundarySew.graph D.wiring
      (D.boundary (BoundaryErase.left k hk)) (D.boundary (BoundaryErase.right k hk))
      (Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)))

instance (D : TurnDisk boundarySize) : Std.Symm D.wiring := by
  induction D with
  | atom p g => exact ⟨fun _ _ h=> Pairing.adj_symm h⟩
  | insert D k hk p g ih =>
    let := ih
    let : Std.Symm p.Adj := ⟨fun _ _ h=>Pairing.adj_symm h⟩
    exact inferInstanceAs (Std.Symm (BoundaryInsert.unionGraph D.wiring p.Adj))
  | attach D E k hk ih ihE =>
    let := ih
    let := ihE
    exact inferInstanceAs (Std.Symm (BoundaryInsert.unionGraph D.wiring E.wiring))
  | sew D k hk ih =>
    let := ih
    exact inferInstanceAs (Std.Symm (BoundarySew.graph D.wiring _ _ _))

def Compatible : {n : ℕ} → TurnDisk n → Prop
  | _,.atom _ _ => True
  | _,.insert D _ _ _ _ => D.Compatible
  | _,.attach D E _ _ => D.Compatible ∧ E.Compatible
  | _,.sew D k hk => D.Compatible ∧
      (Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)) ↔
        Graph.Used D.wiring (D.boundary (BoundaryErase.right k hk))) ∧
      D.gauge (BoundaryErase.right k hk)=D.gauge (BoundaryErase.left k hk)-3

 
def edgeTurn : {n : ℕ} → (D : TurnDisk n) → D.Vertex → D.Vertex → ℤ
  | _,.atom _ g => Pairing.arcTurn g
  | _,.insert D _ _ _ g => fun v w=> match v,w with
      | Sum.inl v,Sum.inl w => D.edgeTurn v w
      | Sum.inr i,Sum.inr j => Pairing.arcTurn g i j
      | _,_ => 0
  | _,.attach D E _ _ => fun v w=> match v,w with
      | Sum.inl v,Sum.inl w => D.edgeTurn v w
      | Sum.inr i,Sum.inr j => E.edgeTurn i j
      | _,_ => 0
  | _,.sew D _ _ => fun v w=> if D.wiring v w then D.edgeTurn v w else 0

lemma boundary_injective (D : TurnDisk boundarySize) : Function.Injective D.boundary := by
  induction D with
  | atom p g => exact Function.injective_id
  | insert D k hk p g ih => exact BoundaryInsert.boundary_injective k hk _ _ ih Function.injective_id
  | attach D E k hk ih ihE => exact BoundaryInsert.boundary_injective k hk _ _ ih ihE
  | sew D k hk ih => exact ih.comp (BoundaryErase.keep k hk).injective

 

theorem potential (D : TurnDisk boundarySize) (hc : D.Compatible)
    (hd : Graph.DrainsBoundary D.wiring D.boundary) :
    ∃ (p : Pairing boundarySize) (P : D.Vertex → ℤ),
      GraphRealizes D.wiring D.boundary p ∧
      (∀ i j,p.Adj i j → P (D.boundary j)-P (D.boundary i)=Pairing.arcTurn D.gauge i j) ∧
      ∀ v w,D.wiring v w → P w-P v=D.edgeTurn v w := by
  induction D with
  | atom p g => exact ⟨p,p.turnPotential g,p.graphRealizes,
      fun _ _ h=>Pairing.turnPotential_of_adj g h,fun _ _ h=>Pairing.turnPotential_of_adj g h⟩
  | @insert n m D k hk t g ih =>
    obtain ⟨p,P,hp,ha,he⟩:=ih hc
      (BoundaryInsert.drains_old D.boundary id k hk hd)
    refine ⟨BoundaryInsert.pairing k hk p t,Sum.elim P (t.turnPotential g),
      BoundaryInsert.realizes k hk hp t.graphRealizes,
      BoundaryInsert.potential k hk _ _ p t D.gauge g P (t.turnPotential g) ha
        (fun _ _ h=>Pairing.turnPotential_of_adj g h),?_⟩
    rintro (v|v) (w|w) hvw
    · exact he _ _ hvw
    · exact hvw.elim
    · exact hvw.elim
    · exact Pairing.turnPotential_of_adj g hvw
  | @attach n m D E k hk ih ihE =>
    obtain ⟨p,P,hp,ha,he⟩:=ih hc.1
      (BoundaryInsert.drains_old D.boundary E.boundary k hk hd)
    obtain ⟨t,Q,ht,hb,hf⟩:=ihE hc.2
      (BoundaryInsert.drains_fresh D.boundary E.boundary k hk hd)
    refine ⟨BoundaryInsert.pairing k hk p t,Sum.elim P Q,
      BoundaryInsert.realizes k hk hp ht,
      BoundaryInsert.potential k hk _ _ p t D.gauge E.gauge P Q ha hb,?_⟩
    rintro (v|v) (w|w) hvw
    · exact he _ _ hvw
    · exact hvw.elim
    · exact hvw.elim
    · exact hf _ _ hvw
  | @sew n D k hk ih =>
    obtain ⟨hc,hmatch,hg⟩:=hc
    have hdold : Graph.DrainsBoundary D.wiring D.boundary := by
      apply Graph.drains_before_sewing D.boundary _ (s:=(D.sew k hk).wiring)
        (fun _ _ h=>Or.inl h) ?_ (fun j=>⟨BoundaryErase.keep k hk j,rfl⟩) hd
      intro v w hvw
      change D.wiring v w ∨ (_ ∧ _) at hvw
      rcases hvw with h|⟨_,h⟩
      · exact Or.inl h
      · rcases h with ⟨rfl,_⟩|⟨rfl,_⟩
        · exact Or.inr ⟨BoundaryErase.left k hk,rfl⟩
        · exact Or.inr ⟨BoundaryErase.right k hk,rfl⟩
    obtain ⟨p,P,hp,ha,he⟩:=ih hc hdold
    have hpused (i : Fin (n+2)) :
        p.Occupied i ↔ Graph.Used D.wiring (D.boundary i) :=
      (hp.boundary_used_iff D.boundary_injective i).symm
    have hm : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk) :=
      (hpused _).trans (hmatch.trans (hpused _).symm)
    have hgraph : BoundarySew.graph D.wiring (D.boundary (BoundaryErase.left k hk))
        (D.boundary (BoundaryErase.right k hk)) (p.Occupied (BoundaryErase.left k hk))=
        (D.sew k hk).wiring := by
      simp only [wiring,hpused]
      rfl
    obtain ⟨q,Q,hq,hArc,hOld,hWire⟩:=BoundarySew.transport_direct p k hk hp D.boundary_injective
      hm D.gauge hg P ha (by rwa [hgraph])
    refine ⟨q,Q,by rwa [hgraph] at hq,hArc,?_⟩
    intro v w hvw
    change Q w-Q v=if D.wiring v w then D.edgeTurn v w else 0
    by_cases hv : D.wiring v w
    · rw [ite_eq_left hv,hOld v w hv,he v w hv]
    · rw [ite_eq_right hv]
      change D.wiring v w ∨ (_ ∧ _) at hvw
      obtain ⟨hu,hw⟩:=hvw.resolve_left hv
      have hh:=hWire ((hpused _).mpr hu)
      rcases hw with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega

end TurnDisk
end
end CriticalStrip.Diagram

end OAI
