import Mathlib
import OAI.Combinatorics.StripMass.HalfTurn

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

 
def turnRow (N j : ℕ) : ℕ := if j<N then N-1-j else j

@[simp] lemma turnRow_involutive (N j : ℕ) : turnRow N (turnRow N j)=j := by
  by_cases hj : j<N
  · have hj' : N-1-j<N := by omega
    simp only [turnRow,hj,hj',ite_true]
    omega
  · simp only [turnRow,hj,ite_false]

 
def turnCell (N : ℕ) (b : ℤ) : Cell ≃ Cell where
  toFun q := (b-q.1,turnRow N q.2)
  invFun q := (b-q.1,turnRow N q.2)
  left_inv := by rintro ⟨i,j⟩; simp only [sub_sub_cancel,turnRow_involutive]
  right_inv := by rintro ⟨i,j⟩; simp only [sub_sub_cancel,turnRow_involutive]

namespace Diagram.Tile
@[simp] lemma turn_nonvacant (t : Tile) : t.turn≠.vacant ↔ t≠.vacant := by cases t <;> decide
end Diagram.Tile

namespace HoneycombAssignment
variable {N : ℕ}

def weight (D : HoneycombAssignment N) : ℝ :=
  ∏ᶠ q : Cell,(physicalWeights (2*Diagram.lambda)).tile (D.tile q)

lemma turn_tile_all (D : HoneycombAssignment N) (b : ℤ) (q : Cell) :
    (D.turn b).tile q=(D.tile (turnCell N b q)).turn := by
  rcases q with ⟨i,j⟩
  by_cases hj : j<N
  · exact D.turn_tile b i j hj |>.trans (by simp only [turnCell,turnRow,hj,ite_true,Equiv.coe_fn_mk])
  · simp only [turn,turnCell,Equiv.coe_fn_mk,turnRow,hj,ite_false,D.outside (b-i) j (by omega),Tile.turn_vacant]

lemma turn_weight (D : HoneycombAssignment N) (b : ℤ) : (D.turn b).weight=D.weight := by
  unfold weight
  simp_rw [D.turn_tile_all b,Tile.turn_weight]
  exact finprod_comp_equiv (turnCell N b) (f:=fun q : Cell=>(physicalWeights (2*Diagram.lambda)).tile (D.tile q))

lemma turn_tileSupport (D : HoneycombAssignment N) (b : ℤ) :
    (D.turn b).tileSupport=turnCell N b ⁻¹' D.tileSupport := by
  ext q
  change ((D.turn b).tile q≠.vacant) ↔ D.tile (turnCell N b q)≠.vacant
  rw [D.turn_tile_all b,Tile.turn_nonvacant]

 
def Fits (D : HoneycombAssignment N) (m : ℕ) : Prop :=
  ∀q : Cell,D.tile q≠.vacant → -(m:ℤ)≤q.1 ∧ q.1<(m:ℤ)

lemma Fits.mono {D : HoneycombAssignment N} {m l : ℕ} (h : D.Fits m) (hm : m≤l) :
    D.Fits l := by
  intro q hq
  obtain ⟨h₁,h₂⟩:=h q hq
  constructor <;> omega

lemma exists_fits (D : HoneycombAssignment N) (h : D.tileSupport.Finite) : ∃m,D.Fits m := by
  let F:=h.toFinset
  refine ⟨F.sup (fun q=>q.1.natAbs+1),?_⟩
  intro q hq
  have hm : q∈F := h.mem_toFinset.mpr hq
  have hs : q.1.natAbs+1≤F.sup (fun q=>q.1.natAbs+1) := Finset.le_sup (f:=fun q : Cell=>q.1.natAbs+1) hm
  have hi : q.1≤(q.1.natAbs:ℤ) := Int.le_natAbs
  have hi' : -q.1≤(q.1.natAbs:ℤ) := by have ht : -q.1≤((-q.1).natAbs:ℤ) := Int.le_natAbs; simpa only [Int.natAbs_neg] using ht
  constructor <;> omega

lemma Fits.vacant_left {D : HoneycombAssignment N} {m k : ℕ} (h : D.Fits m) (hk : m≤k)
    (j : ℕ) : D.tile (-1-(k:ℤ),j)=.vacant := by
  by_contra he
  have hh:=(h _ he).1
  omega

lemma Fits.vacant_right {D : HoneycombAssignment N} {m k : ℕ} (h : D.Fits m) (hk : m≤k)
    (j : ℕ) : D.tile ((k:ℤ),j)=.vacant := by
  by_contra he
  have hh:=(h _ he).2
  omega

def leftClip (D : HoneycombAssignment N) (m : ℕ) : Fin m → Configuration N :=
  fun k j=>D.tile (-1-(k.val:ℤ),j.val)

def rightClip (D : HoneycombAssignment N) (m : ℕ) : Fin m → Configuration N :=
  fun k j=>(D.tile ((k.val:ℤ),j.val)).horizontal

lemma read_leftClip (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) (k : ℕ) (j : Fin N) :
    ColumnChain.read (List.ofFn (D.leftClip m)) k j=D.tile (-1-(k:ℤ),j.val) := by
  by_cases hk : k < m
  · simp only [ColumnChain.read,List.getElem?_ofFn,hk,dite_eq_left,Option.getD_some,leftClip]
  · rw [ColumnChain.read_ge _ k (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hk),
      h.vacant_left (by omega)]

lemma read_rightClip (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) (k : ℕ) (j : Fin N) :
    ColumnChain.read (List.ofFn (D.rightClip m)) k j=(D.tile ((k:ℤ),j.val)).horizontal := by
  by_cases hk : k < m
  · simp only [ColumnChain.read,List.getElem?_ofFn,hk,dite_eq_left,Option.getD_some,rightClip]
  · rw [ColumnChain.read_ge _ k (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hk),
      h.vacant_right (by omega)]
    rfl

lemma sewn_clips (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) :
    D.tile=SewnRectangle.tile (List.ofFn (D.leftClip m)) (List.ofFn (D.rightClip m)) := by
  funext ⟨i,j⟩
  by_cases hj : j<N
  · rcases SewnRectangle.split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
    · rw [SewnRectangle.tile_left _ _ k ⟨j,hj⟩,D.read_leftClip m h k ⟨j,hj⟩]
    · rw [SewnRectangle.tile_right _ _ k ⟨j,hj⟩,D.read_rightClip m h k ⟨j,hj⟩,
        Tile.horizontal_involutive]
  · rw [D.outside i j (by omega),SewnRectangle.tile_outside _ _ i j (by omega)]

lemma clips_compatible (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (hn : ∀i,¬(D.tile (i,N-1)).Occupied 3) :
    ColumnChain.LocallyCompatible (List.ofFn (D.leftClip m)) ∧
      ColumnChain.LocallyCompatible (List.ofFn (D.rightClip m)) := by
  constructor
  · constructor
    · intro k j
      rw [D.read_leftClip m h (k+1) j,D.read_leftClip m h k j]
      have hh:=D.horizontal (-1-((k+1:ℕ):ℤ)) j.val
      simpa only [show -1-((k+1:ℕ):ℤ)+1= -1-(k:ℤ) by omega] using hh
    · intro k j hj
      rw [D.read_leftClip m h k j,hj]
      exact hs _
    · intro k j hj
      rw [D.read_leftClip m h k j,show j.val=N-1 by omega]
      exact hn _
    · intro k i j hij
      rw [D.read_leftClip m h k i,D.read_leftClip m h k j,←hij]
      exact D.vertical _ i.val (by omega)
  · constructor
    · intro k j
      rw [D.read_rightClip m h (k+1) j,D.read_rightClip m h k j,
        Tile.horizontal_occupied_two,Tile.horizontal_occupied_one]
      have hh:=D.horizontal (k:ℤ) j.val
      simpa only [Nat.cast_add,Nat.cast_one] using hh.symm
    · intro k j hj
      rw [D.read_rightClip m h k j,Tile.horizontal_occupied_zero,hj]
      exact hs _
    · intro k j hj
      rw [D.read_rightClip m h k j,Tile.horizontal_occupied_three,show j.val=N-1 by omega]
      exact hn _
    · intro k i j hij
      rw [D.read_rightClip m h k i,D.read_rightClip m h k j,
        Tile.horizontal_occupied_three,Tile.horizontal_occupied_zero,←hij]
      exact D.vertical _ i.val (by omega)

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma tileSupport_finite (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a≠b) :
    D.toHoneycombAssignment.tileSupport.Finite := by
  have hb : BoundaryPort.bottom (b-a)≠.bottom 0 := by intro hh; have hh:=BoundaryPort.bottom.inj hh; omega
  have hs:=(D.toArch hN).tileSupport_finite hN hb
  change (D.toHoneycombAssignment.turn b).tileSupport.Finite at hs
  rw [←D.toHoneycombAssignment.turn_turn b,HoneycombAssignment.turn_tileSupport]
  exact hs.preimage (turnCell N b).injective.injOn

lemma extend_fits (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {m : ℕ} (hf : D.toHoneycombAssignment.Fits m) : (D.extend hN hab).Fits m := by
  intro ⟨i,j⟩ hq
  by_cases hj : j=N
  · subst j
    rw [D.extend_last hN hab,NorthExtension.nonvacant _ _ _ hab] at hq
    have ha : D.tile (a,N-1)≠.vacant := by
      intro he
      have hh:=(D.top a).mpr (Or.inl rfl)
      exact Tile.vacant_not_occupied 3 (he ▸ hh)
    have hb : D.tile (b,N-1)≠.vacant := by
      intro he
      have hh:=(D.top b).mpr (Or.inr rfl)
      exact Tile.vacant_not_occupied 3 (he ▸ hh)
    have ha':=(hf _ ha).1
    have hb':=(hf _ hb).2
    constructor <;> dsimp <;> omega
  · have he : (D.extend hN hab).tile (i,j)=D.tile (i,j) := ite_eq_right hj
    exact hf _ (he ▸ hq)

lemma weight_toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    (D.toArch hN).weight=D.toHoneycombAssignment.weight :=
  D.toHoneycombAssignment.turn_weight b

end TopArchConfiguration
end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Graph

lemma glued_reach_right_boundary {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : I)
    {x : V⊕W} (h : Relation.ReflTransGen (Patch.glued r s a b active) x (.inr (b root))) :
    match x with
    | .inl _ => True
    | .inr x => ∃ i,Relation.ReflTransGen s x (b i) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨root,.refl⟩
  | @head x y hxy h ih =>
    cases x with
    | inl x => trivial
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨i,hi,rfl,hy⟩:=hxy
        exact ⟨i,.refl⟩
      | inr y =>
        obtain ⟨i,hi⟩:=ih
        exact ⟨i,hi.head hxy⟩

lemma glued_drainsAt_halves {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : I)
    (h : DrainsAt (Patch.glued r s a b active) (.inr (b root))) :
    DrainsBoundary r a ∧ DrainsBoundary s b := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr,_⟩:=Patch.reach_to_exterior r s a b active (h (.inl v) (.inl w) hvw)
    exact ⟨i,hr⟩
  · intro v w hvw
    exact glued_reach_right_boundary r s a b active root (h (.inr v) (.inr w) hvw)

end Diagram.Graph

namespace HoneycombAssignment
variable {N : ℕ}

lemma clip_occupancies (D : HoneycombAssignment N) (m : ℕ) (hf : D.Fits m)
    (p q : Pairing N)
    (hl : ColumnChain.Runs (empty N) (List.ofFn (D.leftClip m)) p)
    (hr : ColumnChain.Runs (empty N) (List.ofFn (D.rightClip m)) q) :
    (∀i,p.Occupied i ↔ (D.tile (-1,i.val)).Occupied 2) ∧
      (∀i,q.Occupied i ↔ (D.tile (0,i.val)).Occupied 1) := by
  have hp:=(ColumnChain.runs_sound _ _ _ hl).2.2
  have hq:=(ColumnChain.runs_sound _ _ _ hr).2.2
  constructor
  · intro i
    rw [←hp,ColumnChain.support_empty_read,D.read_leftClip m hf]
    norm_num
  · intro i
    rw [←hq,ColumnChain.support_empty_read,D.read_rightClip m hf,Tile.horizontal_occupied_two]
    norm_num

 

lemma clips_runs_glues (D : HoneycombAssignment N) (hN : 0<N) (m : ℕ) (hf : D.Fits m)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (hn : ∀i,¬(D.tile (i,N-1)).Occupied 3)
    (root : Fin N) (ho : (D.tile (0,root.val)).Occupied 1)
    (hd : Graph.DrainsAt D.graph.Adj (up 0 root.val)) :
    ∃p q, ColumnChain.Runs (empty N) (List.ofFn (D.leftClip m)) p ∧
      ColumnChain.Runs (empty N) (List.ofFn (D.rightClip m)) q ∧ p.GluesAt root q := by
  let l:=List.ofFn (D.leftClip m)
  let r:=List.ofFn (D.rightClip m)
  have ht:=D.sewn_clips m hf
  obtain ⟨hcl,hcr⟩:=D.clips_compatible m hf hs hn
  have hu : Graph.Used D.portWiring ((0,root.val),1) := (D.port_used _).mpr ho
  have hd':= (D.port_drains_iff hu).mpr hd
  have hdg := (SewnRectangle.sewn_drains_iff D l r ht hcr
    (.inr (PaddedColumn.boundary root))).mpr hd'
  obtain ⟨hdl,hdr⟩:=Graph.glued_drainsAt_halves (PaddedColumn.wiring l) (PaddedColumn.wiring r)
    PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l) root hdg
  obtain ⟨p,hp⟩:=PaddedColumn.runs_exists hN l ((ColumnChain.compatible_empty_iff _).mpr hcl) hdl
  obtain ⟨q,hq⟩:=PaddedColumn.runs_exists hN r ((ColumnChain.compatible_empty_iff _).mpr hcr) hdr
  have hx:=D.clip_occupancies m hf p q hp hq
  refine ⟨p,q,hp,hq,(SewnRectangle.gluesAt_physical_iff l r p q hp hq D ht root).mpr ⟨?_,?_,hd'⟩⟩
  · exact (hx.1 root).mpr ((D.horizontal (-1) root.val).mpr (by simpa using ho))
  · intro i
    exact (hx.1 i).trans ((D.horizontal (-1) i.val).trans (by simpa using (hx.2 i).symm))

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

 

lemma extend_clips_runs (D : TopArchConfiguration N a b) (hN : 1≤N) (ha : a<0) (hb : 0≤b)
    (m : ℕ) (hf : D.toHoneycombAssignment.Fits m) :
    let E:=D.extend hN (by omega)
    ∃p q, ColumnChain.Runs (empty (N+1)) (List.ofFn (E.leftClip m)) p ∧
      ColumnChain.Runs (empty (N+1)) (List.ofFn (E.rightClip m)) q ∧
      p.GluesAt (Fin.last N) q := by
  dsimp only
  apply HoneycombAssignment.clips_runs_glues _ (by omega) m (D.extend_fits hN (by omega) hf)
  · intro i
    rw [D.extend_base hN (by omega) i 0 (by omega)]
    exact D.bottom i
  · intro i
    rw [show N+1-1=N by omega,D.extend_last hN (by omega)]
    exact NorthExtension.north _ _ _
  · rw [Fin.val_last,D.extend_last hN (by omega),NorthExtension.west _ _ _ (by omega)]
    exact ⟨ha,hb⟩
  · exact D.extend_drains hN (by omega) (le_of_lt ha) hb

end TopArchConfiguration
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace SewnRectangle
variable {N : ℕ}

def leftWeights (N : ℕ) : Fin (N+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin N=>physicalWeights (2*Diagram.lambda)) northInjectionWeights

def rightWeights (N : ℕ) : Fin (N+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin N=>physicalWeights Diagram.lambda) northInjectionWeights

lemma north_row_tile (l r : List (Configuration (N+1))) (kl ll kr lr : ℕ)
    (hl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant)
    (i : ℤ) : tile l r (i,N)=NorthExtension.tile (-1-(kl:ℤ)) kr i := by
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · rw [show tile l r (-1-(k:ℤ),N)=ColumnChain.read l k (Fin.last N) from tile_left l r k (Fin.last N),ColumnChain.north_shape_read l kl ll hl k]
    unfold NorthExtension.tile
    split_ifs <;> first | rfl | omega
  · rw [show tile l r ((k:ℤ),N)=(ColumnChain.read r k (Fin.last N)).horizontal from tile_right l r k (Fin.last N),ColumnChain.north_shape_read r kr lr hr k]
    unfold NorthExtension.tile
    split_ifs <;> first | rfl | omega

lemma runs_cut {l r : List (Configuration (N+1))} {p q : Pairing (N+1)}
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q) :
    ∀i,(ColumnChain.read l 0 i).Occupied 2 ↔ (ColumnChain.read r 0 i).Occupied 2 := by
  intro i
  rw [←ColumnChain.support_empty_read,←ColumnChain.support_empty_read,
    (ColumnChain.runs_sound _ _ _ hl).2.2,(ColumnChain.runs_sound _ _ _ hr).2.2]
  exact hg.2.1 i

 

def northAssignment (l r : List (Configuration (N+1))) (p q : Pairing (N+1))
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0) : HoneycombAssignment (N+1) :=
  assignment l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
    ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1)
    (runs_cut hl hr hg) (physical_from_weights l r hwl hwr).1 (physical_from_weights l r hwl hwr).2

lemma northAssignment_drains (l r : List (Configuration (N+1))) (p q : Pairing (N+1))
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0) :
    Graph.DrainsAt (northAssignment l r p q hl hr hg hwl hwr).graph.Adj (up 0 N) := by
  let D:=northAssignment l r p q hl hr hg hwl hwr
  have hh:=(gluesAt_physical_iff l r p q hl hr D rfl (Fin.last N)).mp hg
  have ho : (D.tile (0,N)).Occupied 1 := by
    change (tile l r ((0:ℕ), (Fin.last N).val)).Occupied 1
    rw [tile_right,Tile.horizontal_occupied_one,←ColumnChain.support_empty_read,
      (ColumnChain.runs_sound _ _ _ hr).2.2]
    exact (hg.2.1 _).mp hg.1
  exact (D.port_drains_iff ((D.port_used _).mpr ho)).mp hh.2.2

 
def northArch (l r : List (Configuration (N+1))) (p q : Pairing (N+1)) (hN : 1≤N)
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0)
    (kl ll kr lr : ℕ)
    (hsl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hsr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant) :
    TopArchConfiguration N (-1-(kl:ℤ)) kr where
  toHoneycombAssignment := (northAssignment l r p q hl hr hg hwl hwr).restrict N (by omega)
  bottom i := by
    rw [HoneycombAssignment.restrict_tile _ _ _ i 0 (by omega)]
    exact south_vacant l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
      ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1) i
  top i := by
    rw [HoneycombAssignment.restrict_tile _ _ _ i (N-1) (by omega)]
    have hh:=(northAssignment l r p q hl hr hg hwl hwr).vertical i (N-1) (by omega)
    rw [show N-1+1=N by omega] at hh
    exact hh.trans (north_south_occupied l r kl ll kr lr hsl hsr i)
  drains := by
    apply HoneycombAssignment.restrict_drains_of_two_top _ hN _ _ (up 0 N) rfl
      (northAssignment_drains l r p q hl hr hg hwl hwr)
      (restrict_finite_support _ l r rfl)
    · exact south_vacant l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
        ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1)
    · exact north_south_occupied l r kl ll kr lr hsl hsr

lemma northArch_extend (l r : List (Configuration (N+1))) (p q : Pairing (N+1)) (hN : 1≤N)
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0)
    (kl ll kr lr : ℕ)
    (hsl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hsr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant) :
    (northArch l r p q hN hl hr hg hwl hwr kl ll kr lr hsl hsr).extend hN (by omega)=
      northAssignment l r p q hl hr hg hwl hwr := by
  apply HoneycombAssignment.ext
  funext ⟨i,j⟩
  by_cases hj : j=N
  · subst j
    rw [TopArchConfiguration.extend_last]
    exact (north_row_tile l r kl ll kr lr hsl hsr i).symm
  · by_cases hn : j<N
    · rw [TopArchConfiguration.extend_base _ _ _ _ _ hn]
      exact HoneycombAssignment.restrict_tile _ _ (by omega) _ _ hn
    · rw [HoneycombAssignment.outside _ i j (by omega),HoneycombAssignment.outside _ i j (by omega)]

end SewnRectangle

 

 


namespace Diagram.ColumnChain
lemma weight_ofFn {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Weights K) (h : Fin m → Configuration n) :
    weight w (List.ofFn h)=∏ k, ∏ j,(w j).tile (h k j) := by
  induction m with
  | zero => simp [weight]
  | succ m ih => rw [List.ofFn_succ,weight,ih,Fin.prod_univ_succ]
end Diagram.ColumnChain

 
def windowCell (N m : ℕ) : (Fin m ⊕ Fin m) × Fin N → Cell
  | (.inl k,j) => (-1-(k.val:ℤ),j.val)
  | (.inr k,j) => ((k.val:ℤ),j.val)

lemma windowCell_injective (N m : ℕ) : Function.Injective (windowCell N m) := by
  rintro ⟨k,j⟩ ⟨l,i⟩ h
  cases k <;> cases l
  all_goals simp only [windowCell,Prod.mk.injEq] at h
  · exact Prod.ext (congrArg Sum.inl (Fin.ext (by omega))) (Fin.ext h.2)
  · omega
  · omega
  · exact Prod.ext (congrArg Sum.inr (Fin.ext (by omega))) (Fin.ext h.2)

lemma windowCell_range (N m : ℕ) (q : Cell) :
    (∃ x,windowCell N m x=q) ↔ -(m:ℤ)≤q.1 ∧ q.1<(m:ℤ) ∧ q.2<N := by
  constructor
  · rintro ⟨⟨k,j⟩,rfl⟩
    cases k <;> dsimp [windowCell] <;> omega
  · rintro ⟨hl,hr,hj⟩
    by_cases hq : q.1<0
    · refine ⟨(.inl ⟨(-1-q.1).toNat,by omega⟩,⟨q.2,hj⟩),?_⟩
      apply Prod.ext <;> dsimp [windowCell]
      omega
    · refine ⟨(.inr ⟨q.1.toNat,by omega⟩,⟨q.2,hj⟩),?_⟩
      apply Prod.ext <;> dsimp [windowCell]
      omega

namespace HoneycombAssignment
variable {N : ℕ}

lemma weight_window (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) :
    D.weight=(∏ k : Fin m,∏ j : Fin N,
      (physicalWeights (2*Diagram.lambda)).tile (D.tile (-1-(k.val:ℤ),j.val))) *
      (∏ k : Fin m,∏ j : Fin N,
      (physicalWeights (2*Diagram.lambda)).tile (D.tile ((k.val:ℤ),j.val))) := by
  let F:=Finset.univ.image (windowCell N m)
  have hs : Function.mulSupport (fun q=>(physicalWeights (2*Diagram.lambda)).tile (D.tile q)) ⊆ (F:Set Cell) := by
    intro q hq
    have ht : D.tile q≠.vacant := by
      intro he
      exact hq (by change (physicalWeights (2*Diagram.lambda)).tile (D.tile q)=1; rw [he]; rfl)
    have hj : q.2<N := by
      by_contra hn
      exact ht (D.outside _ _ (by omega))
    obtain ⟨x,hx⟩ := (windowCell_range N m q).mpr ⟨(h _ ht).1,(h _ ht).2,hj⟩
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩
  rw [weight,finprod_eq_prod_of_mulSupport_subset _ hs]
  rw [Finset.prod_image (by intro x _ y _ he; exact windowCell_injective N m he)]
  rw [Fintype.prod_prod_type,Fintype.prod_sum_type]
  rfl

lemma physical_tile_weight_ne_zero (D : HoneycombAssignment N) (q : Cell) :
    (physicalWeights (2*Diagram.lambda)).tile (D.tile q) ≠ 0 := by
  have ht := D.physical q
  have hr : Diagram.rho≠0 := by simpa only [Diagram.rho,rho] using (ne_of_gt rho_pos)
  rw [physicalWeights_two_lambda]
  generalize D.tile q=t at *
  cases t <;> simp_all [Weights.tile]
end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma extend_left_north_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (hb : 0≤b) (k : ℕ) :
    (northInjectionWeights : Weights ℝ).tile ((D.extend hN hab).tile (-1-(k:ℤ),N))=1 := by
  rw [D.extend_last hN hab]
  unfold NorthExtension.tile
  split_ifs with h₁ h₂ h₃ <;> first | omega | rfl

lemma extend_right_north_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (k : ℕ) :
    (northInjectionWeights : Weights ℝ).tile ((D.extend hN hab).tile ((k:ℤ),N)).horizontal=1 := by
  rw [D.extend_last hN hab]
  unfold NorthExtension.tile
  split_ifs with h₁ h₂ h₃ <;> first | omega | rfl

lemma leftClip_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (hb : 0≤b) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m))=
      ∏ k : Fin m,∏ j : Fin N,
        (physicalWeights (2*Diagram.lambda)).tile (D.tile (-1-(k.val:ℤ),j.val)) := by
  rw [ColumnChain.weight_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fin.prod_univ_castSucc]
  simp only [SewnRectangle.leftWeights,Fin.snoc_last,Fin.snoc_castSucc,
    HoneycombAssignment.leftClip,Fin.val_castSucc,Fin.val_last]
  rw [D.extend_left_north_weight hN hab hb k.val,mul_one]
  apply Finset.prod_congr rfl
  intro j _
  rw [D.extend_base hN hab _ _ j.isLt]

lemma rightClip_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))=
      ∏ k : Fin m,∏ j : Fin N,
        (physicalWeights (2*Diagram.lambda)).tile (D.tile ((k.val:ℤ),j.val)) := by
  rw [ColumnChain.weight_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fin.prod_univ_castSucc]
  simp only [SewnRectangle.rightWeights,Fin.snoc_last,Fin.snoc_castSucc,
    HoneycombAssignment.rightClip,Fin.val_castSucc,Fin.val_last]
  rw [D.extend_right_north_weight hN hab ha k.val,mul_one]
  apply Finset.prod_congr rfl
  intro j _
  rw [D.extend_base hN hab _ _ j.isLt,←Tile.physical_horizontal_weight_two,Tile.horizontal_involutive]

 

lemma clips_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (hb : 0≤b) (m : ℕ) (hf : D.toHoneycombAssignment.Fits m) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m)) *
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))=
      D.toHoneycombAssignment.weight := by
  rw [D.leftClip_weight hN hab hb,D.rightClip_weight hN hab ha]
  exact (D.toHoneycombAssignment.weight_window m hf).symm

lemma clips_weight_ne_zero (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (hb : 0≤b) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m))≠0 ∧
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))≠0 := by
  rw [D.leftClip_weight hN hab hb,D.rightClip_weight hN hab ha]
  constructor <;> apply Finset.prod_ne_zero_iff.mpr <;> intro k _ <;>
    apply Finset.prod_ne_zero_iff.mpr <;> intro j _ <;>
    exact HoneycombAssignment.physical_tile_weight_ne_zero _ _

end TopArchConfiguration
end
end CriticalStrip

end OAI
