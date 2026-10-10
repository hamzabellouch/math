import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleStar

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

def box (lo hi : Vertex) : Finset Vertex :=
  Finset.Icc lo.1 hi.1 ×ˢ Finset.Icc lo.2 hi.2

def anchor (hi : Vertex) : Vertex := (hi.1+1,hi.2+1)

def safeReach (C : Finset Vertex) (x y : Vertex) : Prop :=
  ∃ p : grid.Walk x y, ∀ z∈p.support, z∉C

def exterior (C : Finset Vertex) (hi : Vertex) : Set Vertex :=
  {x | safeReach C x (anchor hi)}

noncomputable def filled (C : Finset Vertex) (lo hi : Vertex) : Finset Vertex := by
  classical
  exact (box lo hi).filter (fun x => x∉exterior C hi)

lemma safe_refl (C : Finset Vertex) (x : Vertex) (hx : x∉C) : safeReach C x x :=
  ⟨.nil,by simpa using hx⟩

lemma safe_symm {C : Finset Vertex} {x y : Vertex} (h : safeReach C x y) : safeReach C y x := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

lemma safe_trans {C : Finset Vertex} {x y z : Vertex}
    (h : safeReach C x y) (h' : safeReach C y z) : safeReach C x z := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := h'
  refine ⟨p.append q,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw|hw
  · exact hp w hw
  · exact hq w hw

lemma safe_adj {C : Finset Vertex} {x y : Vertex} (hx : x∉C) (hy : y∉C)
    (hxy : grid.Adj x y) : safeReach C x y :=
  ⟨.cons hxy .nil,by simpa using And.intro hx hy⟩

lemma safe_start {C : Finset Vertex} {x y : Vertex} (h : safeReach C x y) : x∉C := by
  obtain ⟨p,hp⟩ := h
  exact hp x p.start_mem_support

lemma safe_end {C : Finset Vertex} {x y : Vertex} (h : safeReach C x y) : y∉C :=
  safe_start (safe_symm h)

lemma safe_int_line (C : Finset Vertex) (p : ℤ → Vertex)
    (hp : ∀ i, p i∉C) (hadj : ∀ i, grid.Adj (p i) (p (i+1))) (a b : ℤ) :
    safeReach C (p a) (p b) := by
  have hn : ∀ a : ℤ, ∀ n : ℕ, safeReach C (p a) (p (a+n)) := by
    intro a n
    induction n with
    | zero => simpa using safe_refl C (p a) (hp a)
    | succ n ih =>
      have hh := safe_adj (hp (a+n)) (hp (a+n+1)) (hadj (a+n))
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using safe_trans ih hh
  by_cases h : a ≤ b
  · have he : a+((b-a).toNat:ℤ)=b := by omega
    simpa only [he] using hn a (b-a).toNat
  · have he : b+((a-b).toNat:ℤ)=a := by omega
    exact safe_symm (by simpa only [he] using hn b (a-b).toNat)

lemma safe_row (C : Finset Vertex) (a b j : ℤ) (h : ∀ i, (i,j)∉C) :
    safeReach C (a,j) (b,j) := safe_int_line C (fun i => (i,j)) h (fun i => adj_right i j) a b

lemma safe_col (C : Finset Vertex) (i a b : ℤ) (h : ∀ j, (i,j)∉C) :
    safeReach C (i,a) (i,b) := safe_int_line C (fun j => (i,j)) h (fun j => adj_up i j) a b

lemma mem_box {lo hi x : Vertex} : x∈box lo hi ↔
    lo.1 ≤ x.1 ∧ x.1 ≤ hi.1 ∧ lo.2 ≤ x.2 ∧ x.2 ≤ hi.2 := by
  simp only [box,Finset.mem_product,Finset.mem_Icc]
  tauto

lemma anchor_not_mem (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi) :
    anchor hi∉C := by
  intro h
  have hh := mem_box.mp (hC h)
  simp [anchor] at hh

lemma outside_box_exterior (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi)
    {x : Vertex} (hx : x∉box lo hi) : x∈exterior C hi := by
  have hrow : ∀ t, (t,hi.2+1)∉C := by
    intro t h
    have hh := mem_box.mp (hC h)
    dsimp at hh;omega
  have hcol : ∀ t, (hi.1+1,t)∉C := by
    intro t h
    have hh := mem_box.mp (hC h)
    dsimp at hh;omega
  change safeReach C x (hi.1+1,hi.2+1)
  rw [mem_box] at hx
  by_cases hfirst : lo.1 ≤ x.1 ∧ x.1 ≤ hi.1
  · have hsecond : x.2 < lo.2 ∨ hi.2 < x.2 := by omega
    have hr : ∀ t, (t,x.2)∉C := by
      intro t h
      have hh := mem_box.mp (hC h)
      dsimp at hh;omega
    exact safe_trans (safe_row C x.1 (hi.1+1) x.2 hr)
      (safe_col C (hi.1+1) x.2 (hi.2+1) hcol)
  · have hc : ∀ t, (x.1,t)∉C := by
      intro t h
      have hh := mem_box.mp (hC h)
      dsimp at hh;omega
    exact safe_trans (safe_col C x.1 x.2 (hi.2+1) hc)
      (safe_row C x.1 (hi.1+1) (hi.2+1) hrow)

lemma mem_filled (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi) (x : Vertex) :
    x∈filled C lo hi ↔ x∉exterior C hi := by
  classical
  simp only [filled,Finset.mem_filter]
  exact ⟨And.right,fun h => ⟨by by_contra hh;exact h (outside_box_exterior C lo hi hC hh),h⟩⟩

lemma subset_filled (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi) :
    C ⊆ filled C lo hi := by
  intro x hx
  rw [mem_filled C lo hi hC]
  intro h
  exact safe_start h hx

lemma filled_subset_box (C : Finset Vertex) (lo hi : Vertex) : filled C lo hi ⊆ box lo hi := by
  classical
  exact Finset.filter_subset _ _

lemma exterior_adj {C : Finset Vertex} {hi x y : Vertex} (hx : x∉C)
    (hy : y∈exterior C hi) (hxy : grid.Adj x y) : x∈exterior C hi :=
  safe_trans (safe_adj hx (safe_start hy) hxy) hy

lemma lift_walk {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    (p : G.Walk x y) (hp : ∀ z∈p.support, z∈S) :
    (G.induce S).Reachable ⟨x,hp x p.start_mem_support⟩ ⟨y,hp y p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons x a y h p ih =>
    have hpa : ∀ z∈p.support, z∈S := fun z hz => hp z (by simp [hz])
    have hh : (G.induce S).Adj ⟨x,hp x (by simp)⟩ ⟨a,hpa a p.start_mem_support⟩ := h
    exact hh.reachable.trans (ih hpa)

lemma exterior_connected (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi) :
    (grid.induce (exterior C hi)).Connected := by
  have ha : anchor hi∈exterior C hi := safe_refl C (anchor hi) (anchor_not_mem C lo hi hC)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (grid.induce (exterior C hi))).mpr
  refine ⟨⟨anchor hi,ha⟩,?_⟩
  rintro ⟨x,hx⟩
  obtain ⟨p,hp⟩ := hx
  have hs : ∀ z∈p.support, z∈exterior C hi := by
    intro z hz
    refine ⟨p.dropUntil z hz,?_⟩
    intro w hw
    exact hp w ((p.support_dropUntil_subset_support hz) hw)
  exact (lift_walk p hs).symm

lemma filled_complement_connected (C : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) : (grid.induce ((filled C lo hi:Set Vertex)ᶜ)).Connected := by
  have he : ((filled C lo hi:Set Vertex)ᶜ)=exterior C hi := by
    ext x
    simp only [Set.mem_compl_iff,Finset.mem_coe,mem_filled C lo hi hC,not_not]
  rw [he]
  exact exterior_connected C lo hi hC

lemma grid_connected : grid.Connected := by
  refine { preconnected := ?_, nonempty := ⟨(0,0)⟩ }
  intro x y
  have hh := safe_trans (safe_row ∅ x.1 y.1 x.2 (by simp))
    (safe_col ∅ y.1 x.2 y.2 (by simp))
  exact hh.elim fun p _ => ⟨p⟩

lemma reach_cluster_walk (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi)
    {x b : Vertex} (p : grid.Walk x b) (hb : b∈C) (hx : x∈filled C lo hi) :
    ∃ y, ∃ hy : y∈C, (grid.induce (filled C lo hi:Set Vertex)).Reachable
      ⟨x,hx⟩ ⟨y,subset_filled C lo hi hC hy⟩ := by
  induction p with
  | nil => exact ⟨_,hb,SimpleGraph.Reachable.rfl⟩
  | @cons x a b hxa p ih =>
    by_cases hxc : x∈C
    · exact ⟨x,hxc,SimpleGraph.Reachable.rfl⟩
    · have ha : a∈filled C lo hi := by
        rw [mem_filled C lo hi hC]
        intro he
        exact (mem_filled C lo hi hC x).mp hx (exterior_adj hxc he hxa)
      obtain ⟨y,hy,hpath⟩ := ih hb ha
      have hh : (grid.induce (filled C lo hi:Set Vertex)).Adj ⟨x,hx⟩ ⟨a,ha⟩ := hxa
      exact ⟨y,hy,hh.reachable.trans hpath⟩

lemma reach_cluster (C : Finset Vertex) (hCne : C.Nonempty) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) {x : Vertex} (hx : x∈filled C lo hi) :
    ∃ y, ∃ hy : y∈C, (grid.induce (filled C lo hi:Set Vertex)).Reachable
      ⟨x,hx⟩ ⟨y,subset_filled C lo hi hC hy⟩ := by
  obtain ⟨b,hb⟩ := hCne
  obtain ⟨p⟩ := grid_connected x b
  exact reach_cluster_walk C lo hi hC p hb hx

lemma filled_star_connected (C : Finset Vertex) (hCne : C.Nonempty) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hconn : (star.induce (C:Set Vertex)).Connected) :
    (star.induce (filled C lo hi:Set Vertex)).Connected := by
  classical
  let ι : star.induce (C:Set Vertex) →g star.induce (filled C lo hi:Set Vertex) :=
    ⟨fun x => ⟨x,subset_filled C lo hi hC x.property⟩,fun h => h⟩
  let j : grid.induce (filled C lo hi:Set Vertex) →g star.induce (filled C lo hi:Set Vertex) :=
    ⟨id,fun h => grid_le_star h⟩
  have hn : Nonempty (filled C lo hi:Set Vertex) := by
    obtain ⟨b,hb⟩ := hCne
    exact ⟨⟨b,subset_filled C lo hi hC hb⟩⟩
  refine { preconnected := ?_, nonempty := hn }
  intro x y
  obtain ⟨a,ha,hxa⟩ := reach_cluster C hCne lo hi hC x.property
  obtain ⟨b,hb,hyb⟩ := reach_cluster C hCne lo hi hC y.property
  exact (hxa.map j).trans (((hconn ⟨a,ha⟩ ⟨b,hb⟩).map ι).trans (hyb.map j).symm)

theorem filled_rim_paths (C : Finset Vertex) (hCne : C.Nonempty) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hconn : (star.induce (C:Set Vertex)).Connected) :
    ∀ x∈rim (filled C lo hi), ∀ y∈rim (filled C lo hi),
      ∃ p : grid.Walk x y, (∀ z∈p.support, z∈rim (filled C lo hi)) ∧
        p.length ≤ 8*(filled C lo hi).card := by
  apply star_rim_paths
  · exact hCne.mono (subset_filled C lo hi hC)
  · exact filled_star_connected C hCne lo hi hC hconn
  · exact filled_complement_connected C lo hi hC

end SparseHoles

end

end OAI
