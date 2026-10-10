import Mathlib
import OAI.Combinatorics.StripMass.HoneycombTiles

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N : ℕ}

@[ext] lemma ext {D E : HoneycombAssignment N} (h : D.tile=E.tile) : D=E := by
  cases D; cases E; cases h; rfl

 

lemma ext_graph_boundary (D E : HoneycombAssignment N) (hN : 1≤N)
    (hg : D.graph=E.graph)
    (hb : ∀ i, (D.tile (i,0)).Occupied 0 ↔ (E.tile (i,0)).Occupied 0)
    (ht : ∀ i, (D.tile (i,N-1)).Occupied 3 ↔ (E.tile (i,N-1)).Occupied 3) : D=E := by
  apply ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hm : (D.tile (i,j)).middle=(E.tile (i,j)).middle := by
      apply Bool.eq_iff_iff.mpr
      have hu := tileGraph_middle N D.tile i j
      have hv := tileGraph_middle N E.tile i j
      change (D.graph.Adj (up i j) (down i j) ↔ _) at hu
      change (E.graph.Adj (up i j) (down i j) ↔ _) at hv
      rw [hg] at hu
      exact (by simpa only [hj,true_and] using hu.symm.trans hv)
    have hw (i : ℤ) : (D.tile (i,j)).Occupied 1 ↔ (E.tile (i,j)).Occupied 1 := by
      have hu := tileGraph_west N D.tile i j
      have hv := tileGraph_west N E.tile i j
      change (D.graph.Adj (up i j) (down (i-1) j) ↔ _) at hu
      change (E.graph.Adj (up i j) (down (i-1) j) ↔ _) at hv
      rw [hg] at hu
      simpa only [hj,true_and] using hu.symm.trans hv
    have hs (j : ℕ) (hj : j<N) (hpos : 0<j) :
        (D.tile (i,j)).Occupied 0 ↔ (E.tile (i,j)).Occupied 0 := by
      have hu := tileGraph_south N D.tile i j hpos
      have hv := tileGraph_south N E.tile i j hpos
      change (D.graph.Adj (up i j) (down i (j-1)) ↔ _) at hu
      change (E.graph.Adj (up i j) (down i (j-1)) ↔ _) at hv
      rw [hg] at hu
      simpa only [hj,true_and] using hu.symm.trans hv
    apply Tile.physical_ext (D.physical (i,j)) (E.physical (i,j)) ?_ hm
    intro p
    fin_cases p
    · by_cases h₀ : j=0
      · subst j; exact hb i
      · exact hs j hj (by omega)
    · exact hw i
    · exact (D.horizontal i j).trans ((hw (i+1)).trans (E.horizontal i j).symm)
    · by_cases hn : j+1=N
      · have he : j=N-1 := by omega
        subst j
        exact ht i
      · have hnext : j+1<N := by omega
        exact (D.vertical i j hnext).trans ((hs (j+1) hnext (by omega)).trans (E.vertical i j hnext).symm)
  · rw [D.outside i j (by omega),E.outside i j (by omega)]

end HoneycombAssignment

namespace WireConfiguration
variable {N : ℕ} {b : BoundaryPort}

def physicalTile (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (q : Cell) : Tile :=
  Classical.choose (Tile.existsUnique_physical
    (decide (D.south q.1 q.2)) (decide (D.west q.1 q.2))
    (decide (D.east q.1 q.2)) (decide (D.north q.1 q.2)) (decide (D.middle q.1 q.2))
    (by simpa only [decide_eq_true_eq] using D.up_valid hN hb q.1 q.2)
    (by simpa only [decide_eq_true_eq] using D.down_valid hN hb q.1 q.2))

lemma physicalTile_spec (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    D.physicalTile hN hb (i,j) ≠ .verticalPair ∧
    ((D.physicalTile hN hb (i,j)).Occupied 0 ↔ D.south i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 1 ↔ D.west i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 2 ↔ D.east i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 3 ↔ D.north i j) ∧
    ((D.physicalTile hN hb (i,j)).middle ↔ D.middle i j) := by
  have h := (Classical.choose_spec (Tile.existsUnique_physical
    (decide (D.south i j)) (decide (D.west i j))
    (decide (D.east i j)) (decide (D.north i j)) (decide (D.middle i j))
    (by simpa only [decide_eq_true_eq] using D.up_valid hN hb i j)
    (by simpa only [decide_eq_true_eq] using D.down_valid hN hb i j))).1
  change D.physicalTile hN hb (i,j) ≠ .verticalPair ∧
    ((D.physicalTile hN hb (i,j)).Occupied 0 ↔ decide (D.south i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 1 ↔ decide (D.west i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 2 ↔ decide (D.east i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 3 ↔ decide (D.north i j) = true) ∧
    (D.physicalTile hN hb (i,j)).middle=decide (D.middle i j) at h
  refine ⟨h.1,?_,?_,?_,?_,?_⟩
  · simpa only [decide_eq_true_eq] using h.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.2.2.1
  · rw [h.2.2.2.2.2,decide_eq_true_eq]

 

def toAssignment (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : HoneycombAssignment N where
  tile := D.physicalTile hN hb
  physical q := (D.physicalTile_spec hN hb q.1 q.2).1
  outside i j hj := by
    apply (Tile.eq_vacant_iff _).mpr
    intro p
    have h := D.physicalTile_spec hN hb i j
    have hf := D.flags_outside hN i j hj
    fin_cases p
    · exact fun hp => hf.1 (h.2.1.mp hp)
    · exact fun hp => hf.2.1 (h.2.2.1.mp hp)
    · exact fun hp => hf.2.2.1 (h.2.2.2.1.mp hp)
    · exact fun hp => hf.2.2.2.1 (h.2.2.2.2.1.mp hp)
  horizontal i j := by
    rw [(D.physicalTile_spec hN hb i j).2.2.2.1,
      (D.physicalTile_spec hN hb (i+1) j).2.2.1]
    simp only [east,west,add_sub_cancel_right]
    exact ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  vertical i j hj := by
    rw [(D.physicalTile_spec hN hb i j).2.2.2.2.1,
      (D.physicalTile_spec hN hb i (j+1)).2.1]
    simp only [north,south,show j+1≠N by omega,show j+1≠0 by omega,
      add_tsub_cancel_right]
    exact ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩

lemma toAssignment_up (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) (w : Triangle) :
    (D.toAssignment hN hb).graph.Adj (up i j) w ↔ D.graph.Adj (up i j) w := by
  rw [HoneycombAssignment.up_neighbors]
  change (j<N ∧ ((w=down i j ∧ (D.physicalTile hN hb (i,j)).middle) ∨
    (w=down (i-1) j ∧ (D.physicalTile hN hb (i,j)).Occupied 1) ∨
    (0<j ∧ w=down i (j-1) ∧ (D.physicalTile hN hb (i,j)).Occupied 0))) ↔ _
  rw [(D.physicalTile_spec hN hb i j).2.2.2.2.2,
    (D.physicalTile_spec hN hb i j).2.2.1,(D.physicalTile_spec hN hb i j).2.1]
  constructor
  · rintro ⟨_,⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨hj,rfl,h⟩⟩
    · exact h
    · exact h
    · simpa only [south,ite_eq_right (show j≠0 by omega)] using h
  · intro h
    refine ⟨(D.allowed _ _ h).2.1,?_⟩
    rcases (adjacent_up_iff i j w).mp (D.allowed _ _ h).1 with rfl | rfl | ⟨hj,rfl⟩
    · exact Or.inl ⟨rfl,h⟩
    · exact Or.inr (Or.inl ⟨rfl,h⟩)
    · exact Or.inr (Or.inr ⟨hj,rfl,by simpa only [south,ite_eq_right (show j≠0 by omega)] using h⟩)

@[simp] theorem toAssignment_graph (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : (D.toAssignment hN hb).graph = D.graph := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  rcases v with ⟨i,j,bv⟩
  cases bv
  · rcases w with ⟨k,l,bw⟩
    cases bw
    · constructor
      · intro h
        have ha := (tileGraph_allowed N (D.toAssignment hN hb).tile h).1
        simp [adjacent,upDownAdjacent] at ha
      · intro h
        have ha := (D.allowed _ _ h).1
        simp [adjacent,upDownAdjacent] at ha
    · exact (show (D.toAssignment hN hb).graph.Adj (down i j) (up k l) ↔
          (D.toAssignment hN hb).graph.Adj (up k l) (down i j) from
          ⟨(D.toAssignment hN hb).graph.symm.symm _ _,(D.toAssignment hN hb).graph.symm.symm _ _⟩).trans
          ((D.toAssignment_up hN hb k l (down i j)).trans
          ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩)
  · exact D.toAssignment_up hN hb i j w

lemma toAssignment_bottom (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) :
    ((D.toAssignment hN hb).tile (i,0)).Occupied 0 ↔ i=0 ∨ b=.bottom i := by
  simpa only [toAssignment,south,ite_true] using (D.physicalTile_spec hN hb i 0).2.1

lemma toAssignment_top (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) :
    ((D.toAssignment hN hb).tile (i,N-1)).Occupied 3 ↔ b=.top i := by
  simpa only [toAssignment,north,show N-1+1=N by omega,ite_true] using
    (D.physicalTile_spec hN hb i (N-1)).2.2.2.2.1

end WireConfiguration

 

structure HoneycombConfiguration (N : ℕ) (b : BoundaryPort) extends HoneycombAssignment N where
  bottom : ∀ i, (tile (i,0)).Occupied 0 ↔ i=0 ∨ b=.bottom i
  top : ∀ i, (tile (i,N-1)).Occupied 3 ↔ b=.top i
  drains : ∀ v w, toHoneycombAssignment.graph.Adj v w →
    Relation.ReflTransGen toHoneycombAssignment.graph.Adj v (up 0 0)

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}

@[ext] lemma ext {D E : HoneycombConfiguration N b}
    (h : D.toHoneycombAssignment=E.toHoneycombAssignment) : D=E := by
  cases D; cases E; cases h; rfl

 
def toWire (D : HoneycombConfiguration N b) (hN : 1≤N) : WireConfiguration N (b.vertex N) where
  graph := D.toHoneycombAssignment.graph
  allowed _ _ h := tileGraph_allowed N D.tile h
  two := D.toHoneycombAssignment.two
  source_one := D.toHoneycombAssignment.bottom_one ((D.bottom 0).mpr (Or.inl rfl))
  finish_one := by
    cases b with
    | bottom i => exact D.toHoneycombAssignment.bottom_one ((D.bottom i).mpr (Or.inr rfl))
    | top i => exact D.toHoneycombAssignment.top_one hN ((D.top i).mpr rfl)
  source_used := D.toHoneycombAssignment.bottom_used hN ((D.bottom 0).mpr (Or.inl rfl))
  finish_used := by
    cases b with
    | bottom i => exact D.toHoneycombAssignment.bottom_used hN ((D.bottom i).mpr (Or.inr rfl))
    | top i => exact D.toHoneycombAssignment.top_used hN ((D.top i).mpr rfl)
  drains := D.drains

def ofWire (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : HoneycombConfiguration N b where
  toHoneycombAssignment := D.toAssignment hN hb
  bottom := D.toAssignment_bottom hN hb
  top := D.toAssignment_top hN hb
  drains v w h := by
    have hg := D.toAssignment_graph hN hb
    rw [hg] at h ⊢
    exact D.drains v w h

@[simp] lemma toWire_ofWire (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : (ofWire D hN hb).toWire hN=D := by
  apply WireConfiguration.ext
  exact D.toAssignment_graph hN hb

@[simp] lemma ofWire_toWire (D : HoneycombConfiguration N b) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : ofWire (D.toWire hN) hN hb=D := by
  apply ext
  apply HoneycombAssignment.ext_graph_boundary _ _ hN
  · exact (D.toWire hN).toAssignment_graph hN hb
  · intro i
    exact ((D.toWire hN).toAssignment_bottom hN hb i).trans (D.bottom i).symm
  · intro i
    exact ((D.toWire hN).toAssignment_top hN hb i).trans (D.top i).symm

 

def equivWires (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    HoneycombConfiguration N b ≃ WireConfiguration N (b.vertex N) where
  toFun D := D.toWire hN
  invFun D := ofWire D hN hb
  left_inv D := ofWire_toWire D hN hb
  right_inv D := toWire_ofWire D hN hb

def equivPaths (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    HoneycombConfiguration N b ≃ {p : List Triangle // IsPath N (b.vertex N) p} :=
  (equivWires N b hN hb).trans (WireConfiguration.equivPaths N (b.vertex N) (b.vertex_ne_source hb))

lemma path_spec (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    IsPath N (b.vertex N) (D.toWire hN).path :=
  (D.toWire hN).path_isPath (b.vertex_ne_source hb)

end HoneycombConfiguration

 

 


namespace Diagram

 

lemma physicalWeights_two_lambda :
    physicalWeights (2*lambda) = (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ) := by
  have hL : L (2*lambda)=C := by
    unfold L
    rw [show 2*lambda+2*lambda=4*lambda by ring,
      show 3*lambda+2*lambda=5*lambda by ring,
      sin_four_lambda_eq_one,sin_five_lambda_eq,sin_three_lambda_eq_C,one_mul]
  unfold physicalWeights
  dsimp only
  change (⟨d * _ / _,_,_,_,_⟩ : Weights ℝ) = _
  rw [hL,show 3*lambda-2*lambda=lambda by ring,show 2*lambda-2*lambda=0 by ring,
    show 2*lambda-lambda=lambda by ring,sin_lambda_eq_c,sin_two_lambda_eq_d,
    Real.sin_zero,mul_zero,zero_div,d_mul_c_div_C,show c*d=d*c by ring,
    d_mul_c_div_C]
  change (⟨rho^2,rho^2,d*d/C,0,rho^2⟩ : Weights ℝ) = _
  rw [←pow_two,d_sq_div_C]

lemma Tile.nonvacant_iff_used (t : Tile) : t ≠ .vacant ↔ t.upperUsed ∨ t.lowerUsed := by
  revert t
  decide

lemma Tile.upperUsed_internal (t : Tile) (ht : t ≠ .verticalPair) :
    t.upperUsed → t.Occupied 1 ∨ t.middle := by
  revert t
  decide

lemma Tile.lowerUsed_internal (t : Tile) (ht : t ≠ .verticalPair) :
    t.lowerUsed → t.Occupied 2 ∨ t.middle := by
  revert t
  decide

end Diagram

namespace HoneycombAssignment
variable {N : ℕ}

lemma up_support_iff (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) :
    up i j ∈ D.graph.support ↔ (D.tile (i,j)).upperUsed := by
  change (∃ w, D.graph.Adj (up i j) w) ↔ _
  constructor
  · rintro ⟨w,hw⟩
    apply (Tile.upperUsed_iff _ (D.physical (i,j))).mpr
    rcases (D.up_neighbors i j w).mp hw with ⟨_,h⟩
    rcases h with ⟨_,hm⟩ | ⟨_,he⟩ | ⟨_,_,hs⟩
    · exact Or.inr (Or.inr hm)
    · exact Or.inr (Or.inl he)
    · exact Or.inl hs
  · intro hu
    have hj : j<N := by
      by_contra hn
      rw [D.outside i j (by omega)] at hu
      exact Bool.false_ne_true hu
    rcases Tile.upperUsed_internal _ (D.physical (i,j)) hu with hw | hm
    · exact ⟨down (i-1) j,(D.up_neighbors i j _).mpr ⟨hj,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
    · exact ⟨down i j,(D.up_neighbors i j _).mpr ⟨hj,Or.inl ⟨rfl,hm⟩⟩⟩

lemma down_support_iff (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) :
    down i j ∈ D.graph.support ↔ (D.tile (i,j)).lowerUsed := by
  change (∃ w, D.graph.Adj (down i j) w) ↔ _
  constructor
  · rintro ⟨w,hw⟩
    apply (Tile.lowerUsed_iff _ (D.physical (i,j))).mpr
    rcases (D.down_neighbors i j w).mp hw with ⟨_,h⟩
    rcases h with ⟨_,hm⟩ | ⟨_,he⟩ | ⟨_,_,hs⟩
    · exact Or.inr (Or.inr hm)
    · exact Or.inl he
    · exact Or.inr (Or.inl hs)
  · intro hu
    have hj : j<N := by
      by_contra hn
      rw [D.outside i j (by omega)] at hu
      exact Bool.false_ne_true hu
    rcases Tile.lowerUsed_internal _ (D.physical (i,j)) hu with hw | hm
    · exact ⟨up (i+1) j,(D.down_neighbors i j _).mpr ⟨hj,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
    · exact ⟨up i j,(D.down_neighbors i j _).mpr ⟨hj,Or.inl ⟨rfl,hm⟩⟩⟩

def tileSupport (D : HoneycombAssignment N) : Set Cell := {q | D.tile q ≠ .vacant}

lemma tileSupport_eq_image (D : HoneycombAssignment N) :
    D.tileSupport = (fun v : Triangle => (v.1,v.2.1)) '' D.graph.support := by
  ext ⟨i,j⟩
  change D.tile (i,j) ≠ .vacant ↔ ∃ v ∈ D.graph.support, (v.1,v.2.1)=(i,j)
  rw [Tile.nonvacant_iff_used]
  constructor
  · rintro (hu | hd)
    · exact ⟨up i j,(D.up_support_iff i j).mpr hu,rfl⟩
    · exact ⟨down i j,(D.down_support_iff i j).mpr hd,rfl⟩
  · rintro ⟨⟨a,k,b⟩,hv,he⟩
    have hi : a=i := congrArg Prod.fst he
    have hj : k=j := congrArg Prod.snd he
    subst a k
    cases b
    · exact Or.inr ((D.down_support_iff i j).mp hv)
    · exact Or.inl ((D.up_support_iff i j).mp hv)

 

lemma support_ncard_eq (D : HoneycombAssignment N) (F : Finset Cell)
    (hF : ∀ q, D.tile q ≠ .vacant ↔ q∈F) :
    D.graph.support.ncard =
      ∑ q∈F, ((if (D.tile q).upperUsed then 1 else 0) +
        (if (D.tile q).lowerUsed then 1 else 0) : ℕ) := by
  let U := F.filter (fun q => (D.tile q).upperUsed)
  let L := F.filter (fun q => (D.tile q).lowerUsed)
  let fu : Cell → Triangle := fun q => up q.1 q.2
  let fl : Cell → Triangle := fun q => down q.1 q.2
  have hu : Function.Injective fu := by
    intro q r h
    have hh := congrArg (fun v : Triangle => (v.1,v.2.1)) h
    exact hh
  have hl : Function.Injective fl := by
    intro q r h
    have hh := congrArg (fun v : Triangle => (v.1,v.2.1)) h
    exact hh
  have hd : Disjoint (U.image fu) (L.image fl) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hw
    have hh := congrArg (fun v : Triangle => v.2.2) hr
    exact Bool.false_ne_true hh
  have hs : D.graph.support = ↑(U.image fu ∪ L.image fl) := by
    ext ⟨i,j,b⟩
    cases b
    · change down i j ∈ D.graph.support ↔ _
      rw [D.down_support_iff]
      simp only [Finset.mem_coe,Finset.mem_union,Finset.mem_image,U,L,
        Finset.mem_filter,fu,fl,up,down,Prod.mk.injEq,Bool.true_eq_false,and_false,exists_false,
        false_or,and_true]
      constructor
      · intro h
        exact ⟨(i,j),⟨(hF (i,j)).mp ((Tile.nonvacant_iff_used _).mpr (Or.inr h)),h⟩,rfl,rfl⟩
      · rintro ⟨⟨a,k⟩,⟨_,h⟩,hi,hj⟩
        dsimp only at hi hj
        subst a k; exact h
    · change up i j ∈ D.graph.support ↔ _
      rw [D.up_support_iff]
      simp only [Finset.mem_coe,Finset.mem_union,Finset.mem_image,U,L,
        Finset.mem_filter,fu,fl,up,down,Prod.mk.injEq,Bool.false_eq_true,and_false,exists_false,
        or_false,and_true]
      constructor
      · intro h
        exact ⟨(i,j),⟨(hF (i,j)).mp ((Tile.nonvacant_iff_used _).mpr (Or.inl h)),h⟩,rfl,rfl⟩
      · rintro ⟨⟨a,k⟩,⟨_,h⟩,hi,hj⟩
        dsimp only at hi hj
        subst a k; exact h
  rw [hs,Set.ncard_coe_finset,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hu,Finset.card_image_of_injective _ hl,Finset.sum_add_distrib]
  simp [U,L]

end HoneycombAssignment

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}

lemma tileSupport_finite (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.toHoneycombAssignment.tileSupport.Finite := by
  rw [HoneycombAssignment.tileSupport_eq_image]
  exact ((D.toWire hN).support_finite (b.vertex_ne_source hb)).image _

 

def weight (D : HoneycombConfiguration N b) : ℝ :=
  ∏ᶠ q : Cell, (physicalWeights (2*Diagram.lambda)).tile (D.tile q)

lemma finite_weight_support (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    (Function.mulSupport (fun q : Cell => (physicalWeights (2*Diagram.lambda)).tile (D.tile q))).Finite := by
  apply (D.tileSupport_finite hN hb).subset
  intro q hq
  change D.tile q ≠ .vacant
  intro ht
  exact hq (by simp only [ht,Weights.tile])

 
theorem weight_eq_wire (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.weight=(D.toWire hN).weight := by
  let F := (D.tileSupport_finite hN hb).toFinset
  have hF : ∀ q, D.tile q≠.vacant ↔ q∈F := by
    intro q
    exact ((D.tileSupport_finite hN hb).mem_toFinset).symm
  have he := finprod_eq_prod_of_mulSupport_subset
    (fun q : Cell => (physicalWeights (2*Diagram.lambda)).tile (D.tile q)) (s := F)
  have hw : D.weight = ∏ q∈F, (physicalWeights (2*Diagram.lambda)).tile (D.tile q) := by
    apply he
    intro q hq
    apply (hF q).mp
    intro ht; exact hq (by simp only [ht,Weights.tile])
  rw [hw,physicalWeights_two_lambda]
  change (∏ q∈F, (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ).tile (D.tile q)) = _
  have hw' (q : Cell) :
      (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ).tile (D.tile q) =
        rho ^ ((if (D.tile q).upperUsed then 1 else 0) +
          (if (D.tile q).lowerUsed then 1 else 0) : ℕ) :=
    Tile.physical_weight rho (D.tile q) (D.physical q)
  simp_rw [hw']
  rw [Finset.prod_pow_eq_pow_sum]
  change rho ^ _ = rho ^ D.toHoneycombAssignment.graph.support.ncard
  rw [D.toHoneycombAssignment.support_ncard_eq F hF]

lemma weight_eq_path (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.weight = rho ^ (D.toWire hN).path.length := by
  rw [D.weight_eq_wire hN hb,(D.toWire hN).weight_eq (b.vertex_ne_source hb)]

lemma countable (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    Countable (HoneycombConfiguration N b) :=
  (equivPaths N b hN hb).countable_iff.mpr inferInstance

 
theorem summable_weight_iff (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    Summable (weight (N := N) (b := b)) ↔
      Summable (WireConfiguration.weight (N := N) (finish := b.vertex N)) := by
  have h := (equivWires N b hN hb).summable_iff (f := WireConfiguration.weight)
  have he : WireConfiguration.weight ∘ (equivWires N b hN hb) = weight := by
    funext D
    exact (D.weight_eq_wire hN hb).symm
  rwa [he] at h

lemma tsum_weight (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    ∑' D : HoneycombConfiguration N b, D.weight =
      ∑' D : WireConfiguration N (b.vertex N), D.weight := by
  rw [show (fun D : HoneycombConfiguration N b => D.weight) =
    (fun D => (D.toWire hN).weight) from funext (fun D => D.weight_eq_wire hN hb)]
  exact (equivWires N b hN hb).tsum_eq WireConfiguration.weight

theorem arch_sum (N : ℕ) (hN : 1≤N) (k : ℤ) (hk : k≠0) :
    K N k = ∑' D : HoneycombConfiguration N (.bottom k), D.weight := by
  rw [tsum_weight N (.bottom k) hN (by simpa using hk)]
  exact WireConfiguration.arch_sum N k hk

theorem arch_summable (N : ℕ) (hN : 1≤N) (k : ℤ) (hk : k≠0) :
    Summable (archWeight N k) ↔ Summable (weight (N := N) (b := .bottom k)) := by
  rw [summable_weight_iff N (.bottom k) hN (by simpa using hk)]
  exact WireConfiguration.arch_summable N k hk

theorem bridge_sum (N : ℕ) (hN : 1≤N) (k : ℤ) :
    bridgeKernel N k = ∑' D : HoneycombConfiguration N (.top k), D.weight := by
  rw [tsum_weight N (.top k) hN (by simp)]
  exact WireConfiguration.bridge_sum N hN k

theorem bridge_summable (N : ℕ) (hN : 1≤N) (k : ℤ) :
    Summable (bridgeWeight N k) ↔ Summable (weight (N := N) (b := .top k)) := by
  rw [summable_weight_iff N (.top k) hN (by simp)]
  exact WireConfiguration.bridge_summable N hN k

end HoneycombConfiguration
end
end CriticalStrip

end OAI
