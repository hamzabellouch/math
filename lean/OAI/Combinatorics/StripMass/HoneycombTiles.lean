import Mathlib
import OAI.Combinatorics.StripMass.GraphPath

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators

 
def ValidTriangle (a b m : Prop) : Prop :=
  (¬a ∧ ¬b ∧ ¬m) ∨ (a ∧ b ∧ ¬m) ∨ (a ∧ ¬b ∧ m) ∨ (¬a ∧ b ∧ m)

lemma ValidTriangle.not_three {a b m : Prop} (h : ValidTriangle a b m) : ¬(a ∧ b ∧ m) := by
  unfold ValidTriangle at h
  tauto

lemma ValidTriangle.one_off {a b m : Prop} (h : ValidTriangle a b m) (ha : a) :
    (b ∧ ¬m) ∨ (¬b ∧ m) := by
  unfold ValidTriangle at h
  tauto

lemma ValidTriangle.of_not_three_not_one {a b m : Prop}
    (h₃ : ¬(a ∧ b ∧ m)) (ha : a → b ∨ m) (hb : b → a ∨ m) (hm : m → a ∨ b) :
    ValidTriangle a b m := by
  unfold ValidTriangle
  tauto

namespace Tile

 

def middle : Tile → Bool
  | .vertical₀ | .vertical₁ | .diagonal₀ | .diagonal₁ => true
  | _ => false

def upperUsed : Tile → Bool
  | .vacant | .cup => false
  | _ => true

def lowerUsed : Tile → Bool
  | .vacant | .cap => false
  | _ => true

lemma physical_up (t : Tile) (h : t ≠ .verticalPair) :
    ValidTriangle (t.Occupied 0) (t.Occupied 1) t.middle := by
  revert t
  unfold ValidTriangle
  decide

lemma physical_down (t : Tile) (h : t ≠ .verticalPair) :
    ValidTriangle (t.Occupied 2) (t.Occupied 3) t.middle := by
  revert t
  unfold ValidTriangle
  decide

lemma upperUsed_iff (t : Tile) (h : t ≠ .verticalPair) :
    t.upperUsed ↔ t.Occupied 0 ∨ t.Occupied 1 ∨ t.middle := by
  revert t
  decide

lemma lowerUsed_iff (t : Tile) (h : t ≠ .verticalPair) :
    t.lowerUsed ↔ t.Occupied 2 ∨ t.Occupied 3 ∨ t.middle := by
  revert t
  decide

lemma physical_ext {t u : Tile} (ht : t ≠ .verticalPair) (hu : u ≠ .verticalPair)
    (h : ∀ i, t.Occupied i ↔ u.Occupied i) (hm : t.middle=u.middle) : t=u := by
  revert t u
  decide

 

theorem existsUnique_physical (s w e n m : Bool)
    (hu : ValidTriangle s w m) (hd : ValidTriangle e n m) :
    ∃! t : Tile, t ≠ .verticalPair ∧
      (t.Occupied 0 ↔ s) ∧ (t.Occupied 1 ↔ w) ∧
      (t.Occupied 2 ↔ e) ∧ (t.Occupied 3 ↔ n) ∧ t.middle=m := by
  have hex : ∃ t : Tile, t ≠ .verticalPair ∧
      (t.Occupied 0 ↔ s) ∧ (t.Occupied 1 ↔ w) ∧
      (t.Occupied 2 ↔ e) ∧ (t.Occupied 3 ↔ n) ∧ t.middle=m := by
    cases s <;> cases w <;> cases e <;> cases n <;> cases m <;>
      simp_all only [ValidTriangle, Bool.false_eq_true, not_false_eq_true, not_true,
        and_false, and_true, or_false, false_or]
    all_goals first
      | exact ⟨.vacant, by decide⟩
      | exact ⟨.vertical₀, by decide⟩
      | exact ⟨.vertical₁, by decide⟩
      | exact ⟨.diagonal₀, by decide⟩
      | exact ⟨.diagonal₁, by decide⟩
      | exact ⟨.cap, by decide⟩
      | exact ⟨.cup, by decide⟩
      | exact ⟨.capCup, by decide⟩
  obtain ⟨t,ht⟩ := hex
  refine ⟨t,ht,?_⟩
  intro u hu
  apply physical_ext hu.1 ht.1 ?_ (hu.2.2.2.2.2.trans ht.2.2.2.2.2.symm)
  intro i
  fin_cases i
  · exact hu.2.1.trans ht.2.1.symm
  · exact hu.2.2.1.trans ht.2.2.1.symm
  · exact hu.2.2.2.1.trans ht.2.2.2.1.symm
  · exact hu.2.2.2.2.1.trans ht.2.2.2.2.1.symm

 
lemma physical_weight (r : ℝ) (t : Tile) (h : t ≠ .verticalPair) :
    (Weights.mk (r^2) (r^2) r 0 (r^2)).tile t =
      r ^ ((if t.upperUsed then 1 else 0) + (if t.lowerUsed then 1 else 0) : ℕ) := by
  cases t <;> simp_all [Weights.tile,upperUsed,lowerUsed]

end Tile
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

abbrev Cell := ℤ × ℕ

 

def upDownWire (t : Cell → Tile) (v w : Triangle) : Prop :=
  v.2.2=true ∧ w.2.2=false ∧
  ((v.2.1=w.2.1 ∧
     ((w.1=v.1 ∧ (t (v.1,v.2.1)).middle) ∨
      (w.1+1=v.1 ∧ (t (v.1,v.2.1)).Occupied 1))) ∨
   (v.2.1=w.2.1+1 ∧ v.1=w.1 ∧ (t (v.1,v.2.1)).Occupied 0))

def tileGraph (N : ℕ) (t : Cell → Tile) : SimpleGraph Triangle where
  Adj v w := v.2.1<N ∧ w.2.1<N ∧ (upDownWire t v w ∨ upDownWire t w v)
  symm := ⟨fun v w h => ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨by
    intro v h
    rcases h.2.2 with h | h <;> exact Bool.noConfusion (h.1.symm.trans h.2.1)⟩

lemma tileGraph_allowed (N : ℕ) (t : Cell → Tile) {v w : Triangle}
    (h : (tileGraph N t).Adj v w) : adjacent v w ∧ v.2.1<N ∧ w.2.1<N := by
  refine ⟨?_,h.1,h.2.1⟩
  have hu : ∀ v w, upDownWire t v w → upDownAdjacent v w := by
    intro v w ⟨hv,hw,h⟩
    refine ⟨hv,hw,?_⟩
    rcases h with ⟨hj,hk⟩ | ⟨hj,hk,ho⟩
    · exact Or.inl ⟨hj,hk.imp And.left And.left⟩
    · exact Or.inr ⟨hj,hk⟩
  exact h.2.2.imp (hu v w) (hu w v)

lemma tileGraph_middle (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) :
    (tileGraph N t).Adj (up i j) (down i j) ↔ j<N ∧ (t (i,j)).middle := by
  simp [tileGraph,upDownWire,up,down]

lemma tileGraph_west (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) :
    (tileGraph N t).Adj (up i j) (down (i-1) j) ↔ j<N ∧ (t (i,j)).Occupied 1 := by
  simp [tileGraph,upDownWire,up,down]

lemma tileGraph_south (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) (hj : 0<j) :
    (tileGraph N t).Adj (up i j) (down i (j-1)) ↔ j<N ∧ (t (i,j)).Occupied 0 := by
  have hn : j ≠ j-1 := by omega
  have hpred : j-1+1=j := by omega
  have hbound : j<N → j-1<N := by omega
  simp [tileGraph,upDownWire,up,down,hn,hpred,and_left_comm]
  exact fun hj _ => hbound hj

lemma tileGraph_up (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) (w : Triangle) :
    (tileGraph N t).Adj (up i j) w ↔ j<N ∧
      ((w=down i j ∧ (t (i,j)).middle) ∨
       (w=down (i-1) j ∧ (t (i,j)).Occupied 1) ∨
       (0<j ∧ w=down i (j-1) ∧ (t (i,j)).Occupied 0)) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rcases (adjacent_up_iff i j w).mp (tileGraph_allowed N t h).1 with rfl | rfl | ⟨hj,rfl⟩
    · exact Or.inl ⟨rfl,((tileGraph_middle N t i j).mp h).2⟩
    · exact Or.inr (Or.inl ⟨rfl,((tileGraph_west N t i j).mp h).2⟩)
    · exact Or.inr (Or.inr ⟨hj,rfl,((tileGraph_south N t i j hj).mp h).2⟩)
  · rintro ⟨hj,⟨rfl,hm⟩ | ⟨rfl,hm⟩ | ⟨hpos,rfl,hm⟩⟩
    · exact (tileGraph_middle N t i j).mpr ⟨hj,hm⟩
    · exact (tileGraph_west N t i j).mpr ⟨hj,hm⟩
    · exact (tileGraph_south N t i j hpos).mpr ⟨hj,hm⟩

 
structure HoneycombAssignment (N : ℕ) where
  tile : Cell → Tile
  physical : ∀ q, tile q ≠ .verticalPair
  outside : ∀ i j, N≤j → tile (i,j)=.vacant
  horizontal : ∀ i j, (tile (i,j)).Occupied 2 ↔ (tile (i+1,j)).Occupied 1
  vertical : ∀ i j, j+1<N → ((tile (i,j)).Occupied 3 ↔ (tile (i,j+1)).Occupied 0)

namespace HoneycombAssignment
variable {N : ℕ}

def graph (D : HoneycombAssignment N) : SimpleGraph Triangle := tileGraph N D.tile

lemma up_neighbors (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle) :
    D.graph.Adj (up i j) w ↔ j<N ∧
      ((w=down i j ∧ (D.tile (i,j)).middle) ∨
       (w=down (i-1) j ∧ (D.tile (i,j)).Occupied 1) ∨
       (0<j ∧ w=down i (j-1) ∧ (D.tile (i,j)).Occupied 0)) :=
  tileGraph_up N D.tile i j w

lemma down_neighbors (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle) :
    D.graph.Adj (down i j) w ↔ j<N ∧
      ((w=up i j ∧ (D.tile (i,j)).middle) ∨
       (w=up (i+1) j ∧ (D.tile (i,j)).Occupied 2) ∨
       (j+1<N ∧ w=up i (j+1) ∧ (D.tile (i,j)).Occupied 3)) := by
  have hs : ∀ v w, D.graph.Adj v w ↔ D.graph.Adj w v := fun _ _ => ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  have hm := tileGraph_middle N D.tile i j
  have he := tileGraph_west N D.tile (i+1) j
  have hn := tileGraph_south N D.tile i (j+1) (by omega)
  simp only [add_sub_cancel_right] at he hn
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rcases (adjacent_down_iff i j w).mp (tileGraph_allowed N D.tile h).1 with rfl | rfl | rfl
    · exact Or.inl ⟨rfl,(hm.mp (D.graph.symm.symm _ _ h)).2⟩
    · exact Or.inr (Or.inl ⟨rfl,(D.horizontal i j).mpr (he.mp (D.graph.symm.symm _ _ h)).2⟩)
    · have h' := hn.mp (D.graph.symm.symm _ _ h)
      exact Or.inr (Or.inr ⟨h'.1,rfl,(D.vertical i j h'.1).mpr h'.2⟩)
  · rintro ⟨hj,⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨hn',rfl,h⟩⟩
    · exact D.graph.symm.symm _ _ (hm.mpr ⟨hj,h⟩)
    · exact D.graph.symm.symm _ _ (he.mpr ⟨hj,(D.horizontal i j).mp h⟩)
    · exact D.graph.symm.symm _ _ (hn.mpr ⟨hn',(D.vertical i j hn').mp h⟩)

end HoneycombAssignment

lemma atMostTwo_of_three {V : Type*} {r : V → V → Prop} {v a b c : V}
    {A B C : Prop} (h₃ : ¬(A ∧ B ∧ C))
    (h : ∀ w, r v w → (w=a ∧ A) ∨ (w=b ∧ B) ∨ (w=c ∧ C)) :
    ∀ {x y z}, r v x → r v y → r v z → x≠y → z=x ∨ z=y := by
  intro x y z hx hy hz hxy
  rcases h x hx with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases h y hy with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;>
    rcases h z hz with ⟨rfl,hz⟩ | ⟨rfl,hz⟩ | ⟨rfl,hz⟩ <;> tauto

namespace HoneycombAssignment
variable {N : ℕ}

lemma two (D : HoneycombAssignment N) : AtMostTwo D.graph.Adj := by
  intro v x y z hx hy hz hn
  rcases v with ⟨i,j,b⟩
  cases b
  · have h := (Tile.physical_down (D.tile (i,j)) (D.physical (i,j))).not_three
    apply atMostTwo_of_three (a := up i j) (b := up (i+1) j) (c := up i (j+1))
      (A := (D.tile (i,j)).middle) (B := (D.tile (i,j)).Occupied 2) (C := (D.tile (i,j)).Occupied 3)
      (by tauto) (fun w hw => ?_) hx hy hz hn
    rcases (D.down_neighbors i j w).mp hw with ⟨_,h⟩
    exact h.imp id (Or.imp id (fun h => ⟨h.2.1,h.2.2⟩))
  · have h := (Tile.physical_up (D.tile (i,j)) (D.physical (i,j))).not_three
    apply atMostTwo_of_three (a := down i j) (b := down (i-1) j) (c := down i (j-1))
      (A := (D.tile (i,j)).middle) (B := (D.tile (i,j)).Occupied 1) (C := (D.tile (i,j)).Occupied 0)
      (by tauto) (fun w hw => ?_) hx hy hz hn
    rcases (D.up_neighbors i j w).mp hw with ⟨_,h⟩
    exact h.imp id (Or.imp id (fun h => ⟨h.2.1,h.2.2⟩))

lemma bottom_one (D : HoneycombAssignment N) {i : ℤ} (hb : (D.tile (i,0)).Occupied 0) :
    AtMostOne D.graph.Adj (up i 0) := by
  intro x y hx hy
  have h := (Tile.physical_up (D.tile (i,0)) (D.physical (i,0))).one_off hb
  rw [D.up_neighbors] at hx hy
  simp only [lt_self_iff_false,false_and,or_false] at hx hy
  rcases hx.2 with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases hy.2 with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;> tauto

lemma bottom_used (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (hb : (D.tile (i,0)).Occupied 0) : ∃ w, D.graph.Adj (up i 0) w := by
  have h := (Tile.physical_up (D.tile (i,0)) (D.physical (i,0))).one_off hb
  rcases h with ⟨hw,hm⟩ | ⟨hw,hm⟩
  · exact ⟨down (i-1) 0,(D.up_neighbors i 0 _).mpr ⟨by omega,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
  · exact ⟨down i 0,(D.up_neighbors i 0 _).mpr ⟨by omega,Or.inl ⟨rfl,hm⟩⟩⟩

lemma top_one (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (ht : (D.tile (i,N-1)).Occupied 3) : AtMostOne D.graph.Adj (down i (N-1)) := by
  intro x y hx hy
  have h := Tile.physical_down (D.tile (i,N-1)) (D.physical (i,N-1))
  unfold ValidTriangle at h
  rw [D.down_neighbors] at hx hy
  have hn : ¬(N-1+1<N) := by omega
  simp only [hn,false_and,or_false] at hx hy
  rcases hx.2 with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases hy.2 with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;> tauto

lemma top_used (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (ht : (D.tile (i,N-1)).Occupied 3) : ∃ w, D.graph.Adj (down i (N-1)) w := by
  have h := Tile.physical_down (D.tile (i,N-1)) (D.physical (i,N-1))
  have h' : (D.tile (i,N-1)).middle ∨ (D.tile (i,N-1)).Occupied 2 := by
    unfold ValidTriangle at h
    tauto
  rcases h' with hm | he
  · exact ⟨up i (N-1),(D.down_neighbors i (N-1) _).mpr ⟨by omega,Or.inl ⟨rfl,hm⟩⟩⟩
  · exact ⟨up (i+1) (N-1),(D.down_neighbors i (N-1) _).mpr ⟨by omega,Or.inr (Or.inl ⟨rfl,he⟩)⟩⟩

end HoneycombAssignment

 

 


lemma validTriangle_of_neighbors {V : Type*} {r : V → V → Prop} {v a b c : V}
    (h₂ : AtMostTwo r) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (he : ∀ w, r v w → w=a ∨ w=b ∨ w=c)
    (ho : ∀ w, r v w → ∃ z, r v z ∧ z≠w) :
    ValidTriangle (r v a) (r v b) (r v c) := by
  apply ValidTriangle.of_not_three_not_one
  · rintro ⟨ha,hb,hc⟩
    exact (h₂ ha hb hc hab).elim hac.symm hbc.symm
  · intro ha
    obtain ⟨z,hz,hza⟩ := ho a ha
    rcases he z hz with rfl | rfl | rfl
    · exact (hza rfl).elim
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hb
    obtain ⟨z,hz,hzb⟩ := ho b hb
    rcases he z hz with rfl | rfl | rfl
    · exact Or.inl hz
    · exact (hzb rfl).elim
    · exact Or.inr hz
  · intro hc
    obtain ⟨z,hz,hzc⟩ := ho c hc
    rcases he z hz with rfl | rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
    · exact (hzc rfl).elim

lemma validTriangle_with_port {V : Type*} {r : V → V → Prop} {v a b : V} {P : Prop}
    (hab : a≠b) (he : ∀ w, r v w → w=a ∨ w=b)
    (h₁ : P → AtMostOne r v) (hu : P → ∃ w, r v w)
    (ho : ¬P → ∀ w, r v w → ∃ z, r v z ∧ z≠w) :
    ValidTriangle P (r v a) (r v b) := by
  apply ValidTriangle.of_not_three_not_one
  · exact fun ⟨hp,ha,hb⟩ => hab (h₁ hp ha hb)
  · intro hp
    obtain ⟨w,hw⟩ := hu hp
    rcases he w hw with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · intro ha
    by_cases hp : P
    · exact Or.inl hp
    obtain ⟨w,hw,hwa⟩ := ho hp a ha
    rcases he w hw with rfl | rfl
    · exact (hwa rfl).elim
    · exact Or.inr hw
  · intro hb
    by_cases hp : P
    · exact Or.inl hp
    obtain ⟨w,hw,hwb⟩ := ho hp b hb
    rcases he w hw with rfl | rfl
    · exact Or.inr hw
    · exact (hwb rfl).elim

 
inductive BoundaryPort where
  | bottom (index : ℤ)
  | top (index : ℤ)
  deriving DecidableEq

namespace BoundaryPort

def vertex (N : ℕ) : BoundaryPort → Triangle
  | .bottom k => up k 0
  | .top k => down k (N-1)

lemma vertex_ne_source {N : ℕ} (b : BoundaryPort) (hb : b ≠ .bottom 0) :
    b.vertex N ≠ up 0 0 := by
  cases b with
  | bottom k => simpa [vertex,up] using hb
  | top k => simp [vertex,up,down]

lemma up_eq_iff {N j : ℕ} {i : ℤ} {b : BoundaryPort} :
    up i j=b.vertex N ↔ b=.bottom i ∧ j=0 := by
  cases b <;> simp [vertex,up,down,eq_comm]

lemma down_eq_iff {N j : ℕ} {i : ℤ} {b : BoundaryPort} :
    down i j=b.vertex N ↔ b=.top i ∧ j=N-1 := by
  cases b <;> simp [vertex,up,down,eq_comm]

end BoundaryPort

namespace WireConfiguration
variable {N : ℕ} {b : BoundaryPort}

def south (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  if j=0 then i=0 ∨ b=.bottom i else D.graph.Adj (up i j) (down i (j-1))

def west (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (up i j) (down (i-1) j)

def middle (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (up i j) (down i j)

def east (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (down i j) (up (i+1) j)

def north (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  if j+1=N then b=.top i else D.graph.Adj (down i j) (up i (j+1))

lemma up_nonterminal (_D : WireConfiguration N (b.vertex N)) {i : ℤ} {j : ℕ}
    (hj : 0<j) : up i j ≠ up 0 0 ∧ up i j ≠ b.vertex N := by
  constructor
  · simp [up,show j≠0 by omega]
  · simp [BoundaryPort.up_eq_iff,show j≠0 by omega]

lemma down_nonterminal (_D : WireConfiguration N (b.vertex N)) {i : ℤ} {j : ℕ}
    (hj : j+1<N) : down i j ≠ up 0 0 ∧ down i j ≠ b.vertex N := by
  constructor
  · simp [up,down]
  · simp [BoundaryPort.down_eq_iff,show j≠N-1 by omega]

lemma up_valid (D : WireConfiguration N (b.vertex N)) (_hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    ValidTriangle (D.south i j) (D.west i j) (D.middle i j) := by
  have hf := b.vertex_ne_source (N := N) hb
  by_cases hj : j=0
  · subst j
    simp only [south,west,middle]
    apply validTriangle_with_port (a := down (i-1) 0) (b := down i 0)
      (by simp [down])
    · intro w hw
      have ha := (adjacent_up_iff i 0 w).mp (D.allowed _ _ hw).1
      simpa only [lt_self_iff_false,false_and,or_false,false_or,or_comm] using ha
    · rintro (rfl | ht)
      · exact D.source_one
      · subst b; exact D.finish_one
    · rintro (rfl | ht)
      · exact D.source_used
      · subst b; exact D.finish_used
    · intro hn w hw
      apply D.another_neighbor hf hw
      · have h : i≠0 := fun h => hn (Or.inl h)
        simpa [up] using h
      · intro he
        exact hn (Or.inr (BoundaryPort.up_eq_iff.mp he).1)
  · have hpos : 0<j := by omega
    simp only [south,ite_eq_right hj,west,middle]
    apply validTriangle_of_neighbors D.two
      (a := down i (j-1)) (b := down (i-1) j) (c := down i j)
      (by simp [down]; omega) (by simp [down,show j-1≠j by omega]) (by simp [down])
    · intro w hw
      have ha := (adjacent_up_iff i j w).mp (D.allowed _ _ hw).1
      tauto
    · intro w hw
      exact D.another_neighbor hf hw (D.up_nonterminal hpos).1 (D.up_nonterminal hpos).2

lemma down_valid (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    ValidTriangle (D.east i j) (D.north i j) (D.middle i j) := by
  have hf := b.vertex_ne_source (N := N) hb
  have hm : D.middle i j ↔ D.graph.Adj (down i j) (up i j) :=
    ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  by_cases hj : j<N
  · by_cases ht : j+1=N
    · have he : j=N-1 := by omega
      subst j
      simp only [east,north,ite_eq_left ht,hm]
      have h := validTriangle_with_port (r := D.graph.Adj) (v := down i (N-1))
        (a := up (i+1) (N-1)) (b := up i (N-1)) (P := b=.top i)
        (by simp [up]) ?_ ?_ ?_ ?_
      · unfold ValidTriangle at h ⊢; tauto
      · intro w hw
        have ha := (adjacent_down_iff i (N-1) w).mp (D.allowed _ _ hw).1
        rcases ha with ha | ha | rfl
        · exact Or.inr ha
        · exact Or.inl ha
        · have := (D.allowed _ _ hw).2.2; simp only [up] at this; omega
      · intro hb'; subst b; exact D.finish_one
      · intro hb'; subst b; exact D.finish_used
      · intro hn w hw
        exact D.another_neighbor hf hw (by simp [down,up])
          (by intro he; exact hn (BoundaryPort.down_eq_iff.mp he).1)
    · have hnext : j+1<N := by omega
      simp only [east,north,ite_eq_right ht,hm]
      apply validTriangle_of_neighbors D.two
        (a := up (i+1) j) (b := up i (j+1)) (c := up i j)
        (by simp [up]) (by simp [up]) (by simp [up])
      · intro w hw
        have ha := (adjacent_down_iff i j w).mp (D.allowed _ _ hw).1
        tauto
      · intro w hw
        exact D.another_neighbor hf hw (D.down_nonterminal hnext).1 (D.down_nonterminal hnext).2
  · have he : ∀ w, ¬ D.graph.Adj (down i j) w := by
      intro w hw; exact hj (D.allowed _ _ hw).2.1
    have hn : j+1≠N := by omega
    simp only [east,north,ite_eq_right hn,hm,he,ValidTriangle,not_false_eq_true,and_self,true_or]

 
lemma flags_outside (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (i : ℤ) (j : ℕ) (hj : N≤j) :
    ¬ D.south i j ∧ ¬ D.west i j ∧ ¬ D.east i j ∧ ¬ D.north i j ∧ ¬ D.middle i j := by
  have he : ∀ w, ¬ D.graph.Adj (up i j) w := by
    intro w hw; have := (D.allowed _ _ hw).2.1; exact (by omega : ¬j<N) this
  have he' : ∀ w, ¬ D.graph.Adj (down i j) w := by
    intro w hw; have := (D.allowed _ _ hw).2.1; exact (by omega : ¬j<N) this
  simp [south,west,east,north,middle,show j≠0 by omega,show j+1≠N by omega,he,he']

end WireConfiguration
end
end CriticalStrip

end OAI
