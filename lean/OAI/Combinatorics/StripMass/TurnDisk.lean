import Mathlib
import OAI.Combinatorics.StripMass.TurnGate

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

def equiv (k : ℕ) (hk : k≤n) : (Fin n ⊕ Fin m) ≃ Fin (n+m) :=
  Equiv.ofBijective (Sum.elim (old k hk) (fresh k hk)) ⟨by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl ((old k hk).injective h)
    · exact (disjoint k hk i j h).elim
    · exact (disjoint k hk j i h.symm).elim
    · exact congrArg Sum.inr ((fresh k hk).injective h),by
    intro i
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
    · exact ⟨.inl j,rfl⟩
    · exact ⟨.inr j,rfl⟩⟩

@[simp] lemma equiv_old (k : ℕ) (hk : k≤n) (i : Fin n) :
    equiv (m:=m) k hk (.inl i)=old k hk i := rfl
@[simp] lemma equiv_fresh (k : ℕ) (hk : k≤n) (i : Fin m) :
    equiv (m:=m) k hk (.inr i)=fresh k hk i := rfl

lemma pairing_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (u v : Fin (n+m)) :
    (pairing k hk p t).Adj u v ↔ (p.map (old k hk)).Adj u v ∨
      (t.map (fresh k hk)).Adj u v := by
  simp only [Pairing.Adj,pairing,Finset.mem_union]
  tauto

@[simp] lemma pairing_old_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i j : Fin n) : (pairing k hk p t).Adj (old k hk i) (old k hk j) ↔ p.Adj i j := by
  rw [pairing_adj,Pairing.map_adj_image]
  constructor
  · rintro (h|h)
    · exact h
    · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
      exact (disjoint k hk i a ha.symm).elim
  · exact Or.inl

@[simp] lemma pairing_fresh_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i j : Fin m) : (pairing k hk p t).Adj (fresh k hk i) (fresh k hk j) ↔ t.Adj i j := by
  rw [pairing_adj,Pairing.map_adj_image]
  constructor
  · rintro (h|h)
    · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
      exact (disjoint k hk a i ha).elim
    · exact h
  · exact Or.inr

@[simp] lemma pairing_cross_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin n) (j : Fin m) : ¬(pairing k hk p t).Adj (old k hk i) (fresh k hk j) := by
  rw [pairing_adj]
  rintro (h|h)
  · obtain ⟨a,b,_,_,hb⟩ := (Pairing.map_adj _ _ _ _).mp h
    exact disjoint k hk b j hb
  · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
    exact disjoint k hk i a ha.symm

@[simp] lemma pairing_old_occupied (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin n) : (pairing k hk p t).Occupied (old k hk i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cover k hk j
    · exact ⟨j,(pairing_old_adj k hk p t i j).mp hj⟩
    · exact (pairing_cross_adj k hk p t i j hj).elim
  · rintro ⟨j,hj⟩
    exact ⟨old k hk j,(pairing_old_adj k hk p t i j).mpr hj⟩

@[simp] lemma pairing_fresh_occupied (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin m) : (pairing k hk p t).Occupied (fresh k hk i) ↔ t.Occupied i := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cover k hk j
    · exact (pairing_cross_adj k hk p t j i hj.symm).elim
    · exact ⟨j,(pairing_fresh_adj k hk p t i j).mp hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨fresh k hk j,(pairing_fresh_adj k hk p t i j).mpr hj⟩

 
def unionGraph {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) :
    (V ⊕ W) → (V ⊕ W) → Prop
  | .inl v,.inl w => r v w
  | .inr v,.inr w => s v w
  | _,_ => False

instance {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) [Std.Symm r] [Std.Symm s] :
    Std.Symm (unionGraph r s) := ⟨by
    rintro (v|v) (w|w) h
    · exact (symm h : r w v)
    · exact h.elim
    · exact h.elim
    · exact (symm h : s w v)⟩

lemma reach_left {V W : Type*} (r : V → V → Prop) (s : W → W → Prop)
    {v : V} {w : V ⊕ W} (h : Relation.ReflTransGen (unionGraph r s) (.inl v) w) :
    ∃ u, w=.inl u ∧ Relation.ReflTransGen r v u := by
  induction h with
  | refl => exact ⟨v,rfl,.refl⟩
  | @tail y z h he ih =>
    obtain ⟨u,rfl,hu⟩:=ih
    cases z with
    | inl z => exact ⟨z,rfl,hu.tail he⟩
    | inr z => exact he.elim

lemma reach_right {V W : Type*} (r : V → V → Prop) (s : W → W → Prop)
    {v : W} {w : V ⊕ W} (h : Relation.ReflTransGen (unionGraph r s) (.inr v) w) :
    ∃ u, w=.inr u ∧ Relation.ReflTransGen s v u := by
  induction h with
  | refl => exact ⟨v,rfl,.refl⟩
  | @tail y z h he ih =>
    obtain ⟨u,rfl,hu⟩:=ih
    cases z with
    | inl z => exact he.elim
    | inr z => exact ⟨z,rfl,hu.tail he⟩

def boundary {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V) (b : Fin m → W) :
    Fin (n+m) → (V ⊕ W) := fun i=>Sum.map a b ((equiv k hk).symm i)

@[simp] lemma boundary_old {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (i : Fin n) :
    boundary k hk a b (old k hk i)=.inl (a i) := by
  change Sum.map a b ((equiv k hk).symm (equiv k hk (.inl i)))=_
  simp only [Equiv.symm_apply_apply,Sum.map_inl]

@[simp] lemma boundary_fresh {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (i : Fin m) :
    boundary k hk a b (fresh k hk i)=.inr (b i) := by
  change Sum.map a b ((equiv k hk).symm (equiv k hk (.inr i)))=_
  simp only [Equiv.symm_apply_apply,Sum.map_inr]

lemma boundary_injective {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (ha : Function.Injective a) (hb : Function.Injective b) :
    Function.Injective (boundary k hk a b) := by
  intro i j hij
  obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j <;>
    simp only [boundary_old,boundary_fresh,Sum.inl.injEq,Sum.inr.injEq] at hij
  · exact congrArg _ (ha hij)
  · cases hij
  · cases hij
  · exact congrArg _ (hb hij)

lemma realizes {V W : Type*} (k : ℕ) (hk : k≤n)
    {r : V → V → Prop} {s : W → W → Prop} {a : Fin n → V} {b : Fin m → W}
    {p : Pairing n} {t : Pairing m} (hp : GraphRealizes r a p) (ht : GraphRealizes s b t) :
    GraphRealizes (unionGraph r s) (boundary k hk a b) (pairing k hk p t) := by
  constructor
  · rintro (v|v) (w|w) h
    · obtain ⟨i,hi,hr⟩:=hp.no_loop v w h
      refine ⟨old k hk i,(pairing_old_occupied k hk p t i).mpr hi,?_⟩
      rw [boundary_old]
      exact Graph.map_reach Sum.inl (fun _ _ h=>.single h) hr
    · exact h.elim
    · exact h.elim
    · obtain ⟨i,hi,hr⟩:=ht.no_loop v w h
      refine ⟨fresh k hk i,(pairing_fresh_occupied k hk p t i).mpr hi,?_⟩
      rw [boundary_fresh]
      exact Graph.map_reach Sum.inr (fun _ _ h=>.single h) hr
  · intro i j
    obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
      obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j <;>
      simp only [boundary_old,boundary_fresh]
    · rw [pairing_old_adj,(old k hk).injective.eq_iff]
      constructor
      · intro h
        obtain ⟨u,he,hu⟩:=reach_left r s h
        cases he
        exact (hp.reach i j).mp hu
      · intro h
        exact Graph.map_reach Sum.inl (fun _ _ h=>.single h) ((hp.reach i j).mpr h)
    · simp only [disjoint k hk i j,pairing_cross_adj,false_or,iff_false]
      intro h
      obtain ⟨u,he,_⟩:=reach_left r s h
      cases he
    · have hne : fresh k hk i≠old k hk j := (disjoint k hk j i).symm
      have hn : ¬(pairing k hk p t).Adj (fresh k hk i) (old k hk j) :=
        fun h=>pairing_cross_adj k hk p t j i h.symm
      simp only [hne,hn,false_or,iff_false]
      intro h
      obtain ⟨u,he,_⟩:=reach_right r s h
      cases he
    · rw [pairing_fresh_adj,(fresh k hk).injective.eq_iff]
      constructor
      · intro h
        obtain ⟨u,he,hu⟩:=reach_right r s h
        cases he
        exact (ht.reach i j).mp hu
      · intro h
        exact Graph.map_reach Sum.inr (fun _ _ h=>.single h) ((ht.reach i j).mpr h)

def gauge (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) : Fin (n+m) → ℤ :=
  fun i=>Sum.elim g h ((equiv k hk).symm i)

@[simp] lemma gauge_old (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) (i : Fin n) :
    gauge k hk g h (old k hk i)=g i := by
  change Sum.elim g h ((equiv k hk).symm (equiv k hk (.inl i)))=_
  simp only [Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] lemma gauge_fresh (k : ℕ) (hk : k≤n) (g : Fin n → ℤ) (h : Fin m → ℤ) (i : Fin m) :
    gauge k hk g h (fresh k hk i)=h i := by
  change Sum.elim g h ((equiv k hk).symm (equiv k hk (.inr i)))=_
  simp only [Equiv.symm_apply_apply,Sum.elim_inr]

lemma potential {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (p : Pairing n) (t : Pairing m)
    (g : Fin n → ℤ) (h : Fin m → ℤ) (P : V → ℤ) (Q : W → ℤ)
    (hP : ∀ i j,p.Adj i j → P (a j)-P (a i)=Pairing.arcTurn g i j)
    (hQ : ∀ i j,t.Adj i j → Q (b j)-Q (b i)=Pairing.arcTurn h i j) :
    ∀ i j,(pairing k hk p t).Adj i j →
      Sum.elim P Q (boundary k hk a b j)-Sum.elim P Q (boundary k hk a b i)=
        Pairing.arcTurn (gauge k hk g h) i j := by
  intro i j hij
  obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j
  · simp only [pairing_old_adj] at hij
    simpa only [boundary_old,Sum.elim_inl,Pairing.arcTurn,gauge_old,Pairing.turnOrder,
      (old k hk).lt_iff_lt] using hP i j hij
  · exact (pairing_cross_adj k hk p t i j hij).elim
  · exact (pairing_cross_adj k hk p t j i hij.symm).elim
  · simp only [pairing_fresh_adj] at hij
    simpa only [boundary_fresh,Sum.elim_inr,Pairing.arcTurn,gauge_fresh,Pairing.turnOrder,
      (fresh k hk).lt_iff_lt] using hQ i j hij

end BoundaryInsert

 

 


namespace GraphRealizes
variable {V : Type*} {n m : ℕ} {r : V → V → Prop} {b : Fin n → V} {p : Pairing n}

lemma restrict_boundary (hp : GraphRealizes r b p) (f : Fin m ↪o Fin n)
    (hf : ∀ i,p.Occupied i → ∃ j,f j=i) :
    GraphRealizes r (b ∘ f) (p.restrict f) := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩:=hp.no_loop v w hvw
    obtain ⟨j,rfl⟩:=hf i hi
    obtain ⟨i,hi⟩:=hi
    obtain ⟨k,rfl⟩:=hf i ⟨f j,hi.symm⟩
    exact ⟨j,⟨k,(Pairing.restrict_adj _ _ _ _).mpr hi⟩,hr⟩
  · intro i j
    rw [Function.comp_apply,Function.comp_apply,hp.reach,Pairing.restrict_adj,f.injective.eq_iff]

end GraphRealizes

namespace BoundaryErase
variable {n : ℕ}

abbrev keep (k : ℕ) (hk : k≤n) : Fin n ↪o Fin (n+2) := BoundaryInsert.old k hk
abbrev left (k : ℕ) (hk : k≤n) : Fin (n+2) := BoundaryInsert.fresh k hk 0
abbrev right (k : ℕ) (hk : k≤n) : Fin (n+2) := BoundaryInsert.fresh k hk 1

lemma adjacent (k : ℕ) (hk : k≤n) : (left k hk).val+1=(right k hk).val := by
  change (k+0)+1=k+1
  omega

lemma distinct (k : ℕ) (hk : k≤n) : left k hk≠right k hk := by
  intro h
  have hh:=congrArg Fin.val h
  have he:=adjacent k hk
  omega

lemma cover (k : ℕ) (hk : k≤n) (i : Fin (n+2)) :
    (∃ j,keep k hk j=i) ∨ i=left k hk ∨ i=right k hk := by
  obtain h|⟨j,rfl⟩:=BoundaryInsert.cover (m:=2) k hk i
  · exact Or.inl h
  · fin_cases j
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

lemma occupied_cover (k : ℕ) (hk : k≤n) (p : Pairing (n+2))
    (hl : ¬p.Occupied (left k hk)) (hr : ¬p.Occupied (right k hk))
    (i : Fin (n+2)) (hi : p.Occupied i) : ∃ j,keep k hk j=i := by
  obtain h|h|h:=cover k hk i
  · exact h
  · exact (hl (h ▸ hi)).elim
  · exact (hr (h ▸ hi)).elim

lemma restrict_realizes {V : Type*} {r : V → V → Prop} {b : Fin (n+2) → V}
    (k : ℕ) (hk : k≤n) (p : Pairing (n+2)) (hp : GraphRealizes r b p)
    (hl : ¬p.Occupied (left k hk)) (hr : ¬p.Occupied (right k hk)) :
    GraphRealizes r (b ∘ keep k hk) (p.restrict (keep k hk)) :=
  hp.restrict_boundary (keep k hk) (occupied_cover k hk p hl hr)

lemma keep_ne_left (k : ℕ) (hk : k≤n) (i : Fin n) : keep k hk i≠left k hk :=
  BoundaryInsert.disjoint k hk i 0
lemma keep_ne_right (k : ℕ) (hk : k≤n) (i : Fin n) : keep k hk i≠right k hk :=
  BoundaryInsert.disjoint k hk i 1

lemma potential {V : Type*} (k : ℕ) (hk : k≤n) (b : Fin (n+2) → V)
    (p : Pairing (n+2)) (g : Fin (n+2) → ℤ) (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (b j)-P (b i)=Pairing.arcTurn g i j) :
    ∀ i j,(p.restrict (keep k hk)).Adj i j →
      P (b (keep k hk j))-P (b (keep k hk i))=Pairing.arcTurn (g ∘ keep k hk) i j := by
  intro i j hij
  have h:=hP (keep k hk i) (keep k hk j) ((Pairing.restrict_adj _ _ _ _).mp hij)
  simpa only [Pairing.arcTurn,Pairing.turnOrder,(keep k hk).lt_iff_lt,Function.comp_apply] using h

end BoundaryErase

namespace BoundarySew
section Wiring
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin (n+2) → V}

 

def tile (active : Prop) : Tile := if active then .cap else .vacant

lemma tile_no_outputs (active : Prop) : ¬(tile active).Occupied 2 ∧ ¬(tile active).Occupied 3 := by
  by_cases ha : active <;> simp [tile,ha,Tile.Occupied,Tile.Adj,Tile.edges]

lemma tile_inputs (active : Prop) : ((tile active).Occupied 0 ↔ active) ∧
    ((tile active).Occupied 1 ↔ active) := by
  by_cases ha : active <;> simp [tile,ha,Tile.Occupied,Tile.Adj,Tile.edges]

lemma output_vacant (p q : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hq : p.tileStep (BoundaryErase.left k hk) (BoundaryErase.right k hk)
      (BoundaryErase.adjacent k hk) (tile (p.Occupied (BoundaryErase.left k hk)))=some q) :
    ¬q.Occupied (BoundaryErase.left k hk) ∧ ¬q.Occupied (BoundaryErase.right k hk) := by
  have hs := p.tileStep_support (BoundaryErase.left k hk) (BoundaryErase.right k hk)
    (BoundaryErase.adjacent k hk) (tile (p.Occupied (BoundaryErase.left k hk))) q hq
  have ht := tile_no_outputs (p.Occupied (BoundaryErase.left k hk))
  constructor
  · rw [hs]
    simpa only [Pairing.stepSupport,ite_true] using ht.1
  · rw [hs]
    simpa only [Pairing.stepSupport,ite_eq_right (BoundaryErase.distinct k hk).symm,ite_true] using ht.2

 

theorem transport (p : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk))
    (g : Fin (n+2) → ℤ) (hg : g (BoundaryErase.right k hk)=g (BoundaryErase.left k hk)-3)
    (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j)
    (hd : Graph.DrainsBoundary
      (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
        (tile (p.Occupied (BoundaryErase.left k hk))))
      ((CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk)) ∘
        BoundaryErase.keep k hk)) :
    ∃ (q : Pairing n) (Q : V ⊕ Fin 4 → ℤ),
      GraphRealizes
        (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
          (tile (p.Occupied (BoundaryErase.left k hk))))
        ((CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk)) ∘
          BoundaryErase.keep k hk) q ∧
      (∀ i j,q.Adj i j →
        Q (.inl (old (BoundaryErase.keep k hk j)))-Q (.inl (old (BoundaryErase.keep k hk i)))=
          Pairing.arcTurn (g ∘ BoundaryErase.keep k hk) i j) ∧
      (∀ v w,r v w → Q (.inl w)-Q (.inl v)=P w-P v) ∧
      Q (.inl (old (BoundaryErase.left k hk)))=Q (.inr 0) ∧
      Q (.inl (old (BoundaryErase.right k hk)))=Q (.inr 1) ∧
      (p.Occupied (BoundaryErase.left k hk) → Q (.inr 1)=Q (.inr 0)) := by
  let a:=BoundaryErase.left k hk
  let b:=BoundaryErase.right k hk
  let t:=tile (p.Occupied a)
  have hab : a.val+1=b.val := BoundaryErase.adjacent k hk
  have hne : a≠b := BoundaryErase.distinct k hk
  have ht : CutPatch.Compatible (p.cutShape a b) t := by
    rw [p.cutShape_compatible]
    exact ⟨(tile_inputs _).1.symm,hc.symm.trans (tile_inputs _).2.symm⟩
  have hd' : Graph.DrainsBoundary (CompactGate.wiring r old p.Occupied a b t)
      (CompactGate.boundary old a b) := by
    intro v w hvw
    obtain ⟨i,hi⟩:=hd v w hvw
    exact ⟨BoundaryErase.keep k hk i,hi⟩
  obtain ⟨q,hq⟩:=graph_gate_step_exists hp a b hab t ht
    ((CompactGate.contraction hp hinj a b hne t).drains_inv hd')
  have hr : GraphRealizes (CompactGate.wiring r old p.Occupied a b t)
      (CompactGate.boundary old a b) q :=
    (CompactGate.realizes_iff hp hinj a b hne t q).mp ((graph_gate_step_iff hp a b hab t q).mpr hq).2
  obtain ⟨Q,hQ,hOld,hTile,hA,hB⟩:=CompactGate.transport_potential hp a b hab t g g
    (fun _ _ _=>rfl) hq P hP
  obtain ⟨hqa,hqb⟩:=output_vacant p q k hk hq
  refine ⟨q.restrict (BoundaryErase.keep k hk),Q,
    BoundaryErase.restrict_realizes k hk q hr hqa hqb,?_,hOld,hA,hB,?_⟩
  · intro i j hij
    have hqp : ∀ i j,q.Adj i j →
        Q (CompactGate.boundary old a b j)-Q (CompactGate.boundary old a b i)=Pairing.arcTurn g i j := by
      intro i j hij
      rw [hQ,hQ]
      exact Pairing.turnPotential_of_adj g hij
    have hh:=BoundaryErase.potential k hk (CompactGate.boundary old a b) q g Q hqp i j hij
    simpa only [CompactGate.boundary,a,b,ite_eq_right (BoundaryErase.keep_ne_left k hk i),
      ite_eq_right (BoundaryErase.keep_ne_right k hk i),ite_eq_right (BoundaryErase.keep_ne_left k hk j),
      ite_eq_right (BoundaryErase.keep_ne_right k hk j)] using hh
  · intro ha
    have habt : t.Adj 0 1 := by simp [t,a,tile,ha,Tile.Adj,Tile.edges]
    have hh:=hTile 0 1 habt
    change Q (.inr 1)-Q (.inr 0)=g b-g a+3 at hh
    change g b=g a-3 at hg
    omega

end Wiring

 

 


variable {V : Type*} {n : ℕ}

 
def graph (r : V → V → Prop) (a b : V) (active : Prop) (v w : V) : Prop :=
  r v w ∨ active ∧ ((v=a ∧ w=b) ∨ (v=b ∧ w=a))

instance (r : V → V → Prop) [Std.Symm r] (a b : V) (active : Prop) :
    Std.Symm (graph r a b active) := ⟨by
  intro v w h
  rcases h with h|⟨h,h'⟩
  · exact Or.inl (symm h)
  · exact Or.inr ⟨h,h'.elim (fun h=>Or.inr ⟨h.2,h.1⟩) (fun h=>Or.inl ⟨h.2,h.1⟩)⟩⟩

def project (a b : V) : V ⊕ Fin 4 → V
  | .inl v => v
  | .inr i => if i=1 then b else a

variable {r : V → V → Prop} [Std.Symm r] {old : Fin (n+2) → V} {p : Pairing (n+2)}

omit [Std.Symm r] in
lemma project_edge (a b : Fin (n+2)) (_hc : p.Occupied a ↔ p.Occupied b)
    {v w : V ⊕ Fin 4}
    (h : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)) v w) :
    Relation.ReflTransGen (graph r (old a) (old b) (p.Occupied a))
      (project (old a) (old b) v) (project (old a) (old b) w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact .single (Or.inl h)
    | inr j =>
      rcases h with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> simp only [project] <;> exact .refl
  | inr i =>
    cases w with
    | inl w =>
      rcases h with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> simp only [project] <;> exact .refl
    | inr j =>
      change (tile (p.Occupied a)).Adj i j at h
      by_cases ha : p.Occupied a
      · have hh : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
          simpa only [tile,ite_eq_left ha,Tile.Adj,Tile.edges,Finset.mem_singleton,Prod.mk.injEq,and_comm] using h
        rcases hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact .single (Or.inr ⟨ha,Or.inl ⟨rfl,rfl⟩⟩)
        · exact .single (Or.inr ⟨ha,Or.inr ⟨rfl,rfl⟩⟩)
      · simp only [tile,ite_eq_right ha,Tile.vacant_not_adj] at h

lemma include_edge (a b : Fin (n+2)) (hc : p.Occupied a ↔ p.Occupied b)
    {v w : V} (h : graph r (old a) (old b) (p.Occupied a) v w) :
    Relation.ReflTransGen (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)))
      (.inl v) (.inl w) := by
  have forward (ha : p.Occupied a) :
      Relation.ReflTransGen (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)))
        (.inl (old a)) (.inl (old b)) := by
    have h₁ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inl (old a)) (.inr 0) := Or.inl ⟨rfl,rfl,ha⟩
    have h₂ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inr 0) (.inr 1) := by simp [CompactGate.wiring,tile,ha,Tile.Adj,Tile.edges]
    have h₃ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inr 1) (.inl (old b)) := Or.inr ⟨rfl,rfl,hc.mp ha⟩
    exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃
  rcases h with h|⟨ha,h⟩
  · exact .single h
  · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact forward ha
    · exact symm (forward ha)

omit [Std.Symm r] in
lemma used_port (a b : Fin (n+2)) (hc : p.Occupied a ↔ p.Occupied b) {i : Fin 4}
    (hi : Graph.Used (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))) (.inr i)) :
    p.Occupied a ∧ (i=0 ∨ i=1) := by
  obtain ⟨w,hw⟩:=hi
  cases w with
  | inl w =>
    rcases hw with ⟨rfl,rfl,ha⟩|⟨rfl,rfl,hb⟩
    · exact ⟨ha,Or.inl rfl⟩
    · exact ⟨hc.mpr hb,Or.inr rfl⟩
  | inr j =>
    by_cases ha : p.Occupied a
    · have hh : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
        simpa only [CompactGate.wiring,tile,ite_eq_left ha,Tile.Adj,Tile.edges,
          Finset.mem_singleton,Prod.mk.injEq,and_comm] using hw
      exact ⟨ha,hh.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)⟩
    · simp only [CompactGate.wiring,tile,ite_eq_right ha,Tile.vacant_not_adj] at hw

def equivalence (k : ℕ) (hk : k≤n) (hp : GraphRealizes r old p)
    (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk)) :
    Graph.BoundaryEquiv
      (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
        (tile (p.Occupied (BoundaryErase.left k hk))))
      (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
        (p.Occupied (BoundaryErase.left k hk)))
      (CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk) ∘
        BoundaryErase.keep k hk) (old ∘ BoundaryErase.keep k hk) := by
  let a:=BoundaryErase.left k hk
  let b:=BoundaryErase.right k hk
  have hup (i : Fin (n+2)) (hi : p.Occupied i) : Graph.Used r (old i) :=
    (hp.boundary_used_iff hinj i).mpr hi
  refine ⟨project (old a) (old b),Sum.inl,
    fun _ _=>project_edge a b hc,fun _ _=>include_edge a b hc,?_,?_,?_,?_,?_,?_⟩
  · intro i
    simp only [Function.comp_apply,CompactGate.boundary,
      ite_eq_right (BoundaryErase.keep_ne_left k hk i),ite_eq_right (BoundaryErase.keep_ne_right k hk i),project]
  · intro i
    simp only [Function.comp_apply,CompactGate.boundary,
      ite_eq_right (BoundaryErase.keep_ne_left k hk i),ite_eq_right (BoundaryErase.keep_ne_right k hk i)]
  · rintro (v|i) hv
    · obtain ⟨w,hw⟩:=hv
      cases w with
      | inl w => exact ⟨w,Or.inl hw⟩
      | inr j =>
        rcases hw with ⟨rfl,rfl,ha⟩|⟨rfl,rfl,hb⟩
        · obtain ⟨w,hw⟩:=hup a ha; exact ⟨w,Or.inl hw⟩
        · obtain ⟨w,hw⟩:=hup b hb; exact ⟨w,Or.inl hw⟩
    · obtain ⟨ha,hi⟩:=used_port a b hc hv
      rcases hi with rfl|rfl
      · obtain ⟨w,hw⟩:=hup a ha; exact ⟨w,Or.inl hw⟩
      · obtain ⟨w,hw⟩:=hup b (hc.mp ha); exact ⟨w,Or.inl hw⟩
  · rintro v ⟨w,hw⟩
    rcases hw with hw|⟨ha,hw⟩
    · exact ⟨.inl w,hw⟩
    · rcases hw with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨.inr 0,Or.inl ⟨rfl,rfl,ha⟩⟩
      · exact ⟨.inr 1,Or.inr ⟨rfl,rfl,hc.mp ha⟩⟩
  · rintro (v|i) hv
    · exact .refl
    · obtain ⟨ha,hi⟩:=used_port a b hc hv
      rcases hi with rfl|rfl
      · exact .single (Or.inl ⟨rfl,rfl,ha⟩)
      · exact .single (Or.inr ⟨rfl,rfl,hc.mp ha⟩)
  · exact fun _ _=>.refl

 
theorem transport_direct (p : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk))
    (g : Fin (n+2) → ℤ) (hg : g (BoundaryErase.right k hk)=g (BoundaryErase.left k hk)-3)
    (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j)
    (hd : Graph.DrainsBoundary
      (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
        (p.Occupied (BoundaryErase.left k hk))) (old ∘ BoundaryErase.keep k hk)) :
    ∃ (q : Pairing n) (Q : V → ℤ),
      GraphRealizes
        (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
          (p.Occupied (BoundaryErase.left k hk))) (old ∘ BoundaryErase.keep k hk) q ∧
      (∀ i j,q.Adj i j → Q (old (BoundaryErase.keep k hk j))-Q (old (BoundaryErase.keep k hk i))=
        Pairing.arcTurn (g ∘ BoundaryErase.keep k hk) i j) ∧
      (∀ v w,r v w → Q w-Q v=P w-P v) ∧
      (p.Occupied (BoundaryErase.left k hk) → Q (old (BoundaryErase.right k hk))=Q (old (BoundaryErase.left k hk))) := by
  let e:=equivalence k hk hp hinj hc
  obtain ⟨q,Q,hq,hArc,hOld,ha,hb,hab⟩:=transport p k hk hp hinj hc g hg P hP (e.symm.drains hd)
  refine ⟨q,Q ∘ Sum.inl,e.realizes hq,hArc,hOld,?_⟩
  intro hi
  change Q (.inl (old (BoundaryErase.right k hk)))=Q (.inl (old (BoundaryErase.left k hk)))
  rw [ha,hb,hab hi]

end BoundarySew
end
end CriticalStrip.Diagram

end OAI
