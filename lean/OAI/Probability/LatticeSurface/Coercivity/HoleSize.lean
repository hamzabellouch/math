import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma natAbs_sub_triangle (a b c : ℤ) : (a-c).natAbs ≤ (a-b).natAbs+(b-c).natAbs := by
  have hh := Int.natAbs_add_le (a-b) (b-c)
  simpa only [sub_add_sub_cancel] using hh

lemma star_walk_bounds {x y : Vertex} (p : star.Walk x y) :
    (x.1-y.1).natAbs ≤ p.length ∧ (x.2-y.2).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
    have h1 := natAbs_sub_triangle x.1 z.1 y.1
    have h2 := natAbs_sub_triangle x.2 z.2 y.2
    have hx1 := hxz.2.1
    have hx2 := hxz.2.2
    simp only [SimpleGraph.Walk.length_cons]
    constructor <;> omega

lemma cluster_pair_bounds (C : Finset Vertex)
    (hc : (star.induce (C:Set Vertex)).Connected) {x y : Vertex} (hx : x∈C) (hy : y∈C) :
    (x.1-y.1).natAbs ≤ C.card ∧ (x.2-y.2).natAbs ≤ C.card := by
  classical
  obtain ⟨p,hp⟩ := (hc ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
  let inc : star.induce (C:Set Vertex) →g star := ⟨Subtype.val,fun h => h⟩
  let q := p.map inc
  have hq : q.IsPath := hp.map (by intro a b h;exact Subtype.ext h)
  have hsup : q.support.toFinset ⊆ C := by
    intro z hz
    rw [List.mem_toFinset,SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact w.property
  have hlen := Finset.card_le_card hsup
  rw [List.toFinset_card_of_nodup hq.support_nodup,SimpleGraph.Walk.length_support] at hlen
  have hb := star_walk_bounds q
  exact ⟨hb.1.trans (by omega),hb.2.trans (by omega)⟩

def offsetBox (z : Vertex) (n : ℕ) : Finset Vertex :=
  box (z.1-n,z.2-n) (z.1+n,z.2+n)

lemma natAbs_sub_le_iff (a b : ℤ) (n : ℕ) :
    (a-b).natAbs ≤ n ↔ b-(n:ℤ) ≤ a ∧ a ≤ b+n := by
  rw [← Nat.cast_le (α := ℤ),Int.natCast_natAbs,abs_le]
  constructor <;> intro h <;> constructor <;> omega

lemma mem_offsetBox (x z : Vertex) (n : ℕ) :
    x∈offsetBox z n ↔ (x.1-z.1).natAbs ≤ n ∧ (x.2-z.2).natAbs ≤ n := by
  simp only [offsetBox,mem_box,natAbs_sub_le_iff]
  tauto

lemma offsetBox_card (z : Vertex) (n : ℕ) : (offsetBox z n).card=(2*n+1)^2 := by
  simp only [offsetBox,box,Finset.card_product,Int.card_Icc]
  have h1 : z.1+(n:ℤ)+1-(z.1-n)=((2*n+1:ℕ):ℤ) := by push_cast;ring
  have h2 : z.2+(n:ℤ)+1-(z.2-n)=((2*n+1:ℕ):ℤ) := by push_cast;ring
  rw [h1,h2,Int.toNat_natCast]
  ring

lemma filled_in_cluster_ball (C : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hc : (star.induce (C:Set Vertex)).Connected)
    {c : Vertex} (hcC : c∈C) : filled C lo hi ⊆ offsetBox c C.card := by
  apply filled_in_any_box C lo hi _ _ hC
  intro x hx
  exact (mem_offsetBox x c C.card).mpr (cluster_pair_bounds C hc hx hcC)

noncomputable def diameter (H : Finset Vertex) : ℕ :=
  H.sup (fun x => H.sup (fun y => max (x.1-y.1).natAbs (x.2-y.2).natAbs))

lemma le_diameter (H : Finset Vertex) {x y : Vertex} (hx : x∈H) (hy : y∈H) :
    (x.1-y.1).natAbs ≤ diameter H ∧ (x.2-y.2).natAbs ≤ diameter H := by
  have h1 : max (x.1-y.1).natAbs (x.2-y.2).natAbs ≤
      H.sup (fun y => max (x.1-y.1).natAbs (x.2-y.2).natAbs) := Finset.le_sup (f := fun y : Vertex => max (x.1-y.1).natAbs (x.2-y.2).natAbs) hy
  have h2 : H.sup (fun y => max (x.1-y.1).natAbs (x.2-y.2).natAbs) ≤ diameter H :=
    Finset.le_sup (f := fun x : Vertex => H.sup (fun y : Vertex => max (x.1-y.1).natAbs (x.2-y.2).natAbs)) hx
  have h := h1.trans h2
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

lemma diameter_le (H : Finset Vertex) (n : ℕ)
    (h : ∀ x∈H, ∀ y∈H, (x.1-y.1).natAbs ≤ n ∧ (x.2-y.2).natAbs ≤ n) :
    diameter H ≤ n := by
  apply Finset.sup_le
  intro x hx
  apply Finset.sup_le
  intro y hy
  exact max_le (h x hx y hy).1 (h x hx y hy).2

lemma card_le_diameter_sq (H : Finset Vertex) : H.card ≤ (2*diameter H+1)^2 := by
  rcases H.eq_empty_or_nonempty with rfl|hne
  · simp
  obtain ⟨c,hc⟩ := hne
  have hs : H ⊆ offsetBox c (diameter H) := by
    intro x hx
    exact (mem_offsetBox x c _).mpr (le_diameter H hx hc)
  exact (Finset.card_le_card hs).trans_eq (offsetBox_card c _)

lemma filled_diameter_le (C : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hne : C.Nonempty)
    (hc : (star.induce (C:Set Vertex)).Connected) :
    diameter (filled C lo hi) ≤ 2*C.card := by
  obtain ⟨c,hcC⟩ := hne
  apply diameter_le
  intro x hx y hy
  obtain ⟨hx1,hx2⟩ := (mem_offsetBox x c C.card).mp (filled_in_cluster_ball C lo hi hC hc hcC hx)
  obtain ⟨hy1,hy2⟩ := (mem_offsetBox y c C.card).mp (filled_in_cluster_ball C lo hi hC hc hcC hy)
  have h1 := natAbs_sub_triangle x.1 c.1 y.1
  have h2 := natAbs_sub_triangle x.2 c.2 y.2
  have hsym (a b : ℤ) : (a-b).natAbs=(b-a).natAbs := by
    rw [← Int.natAbs_neg (a-b),neg_sub]
  rw [hsym c.1 y.1] at h1
  rw [hsym c.2 y.2] at h2
  constructor <;> omega

def incidentClosed (H : Finset Vertex) (z : Vertex) : Prop := z∈H ∨ incident H z

lemma incident_filled_location (C : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hc : (star.induce (C:Set Vertex)).Connected)
    {c z : Vertex} (hcC : c∈C) (hz : incidentClosed (filled C lo hi) z) :
    c∈offsetBox z (C.card+1) := by
  have hx : ∃ x∈filled C lo hi, (z.1-x.1).natAbs ≤ 1 ∧ (z.2-x.2).natAbs ≤ 1 := by
    rcases hz with hz|⟨x,hx,hxz⟩
    · exact ⟨z,hz,by simp,by simp⟩
    · have hh := grid_le_star hxz.symm
      exact ⟨x,hx,hh.2.1,hh.2.2⟩
  obtain ⟨x,hx,hxz1,hxz2⟩ := hx
  have hh := (mem_offsetBox x c C.card).mp (filled_in_cluster_ball C lo hi hC hc hcC hx)
  have h1 := natAbs_sub_triangle z.1 x.1 c.1
  have h2 := natAbs_sub_triangle z.2 x.2 c.2
  have hsym (a b : ℤ) : (a-b).natAbs=(b-a).natAbs := by
    rw [← Int.natAbs_neg (a-b),neg_sub]
  rw [mem_offsetBox,hsym c.1 z.1,hsym c.2 z.2]
  constructor <;> omega

end SparseHoles

end

end OAI
