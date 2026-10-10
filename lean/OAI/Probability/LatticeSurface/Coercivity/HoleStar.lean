import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

def star : SimpleGraph Vertex where
  Adj x y := x≠y ∧ (x.1-y.1).natAbs ≤ 1 ∧ (x.2-y.2).natAbs ≤ 1
  symm := ⟨by
    intro x y h
    have hab (a b : ℤ) : (a-b).natAbs=(b-a).natAbs := by
      rw [← Int.natAbs_neg (a-b),neg_sub]
    exact ⟨h.1.symm,by simpa only [hab y.1 x.1] using h.2.1,
      by simpa only [hab y.2 x.2] using h.2.2⟩⟩
  loopless := ⟨by intro x h;exact h.1 rfl⟩

lemma grid_le_star : grid ≤ star := by
  intro x y h
  change (x.1-y.1).natAbs+(x.2-y.2).natAbs=1 at h
  refine ⟨?_,by omega,by omega⟩
  intro he;subst y;simp at h

lemma potential_const_star (B : Finset Vertex) (S : Set Vertex) (hS : S ⊆ rim B)
    (f : Vertex → ZMod 2)
    (hf : ∀ x y, grid.Adj x y → f y-f x=label B S x y)
    {x y : Vertex} (hx : x∈B) (hy : y∈B) (hxy : star.Adj x y) : f x=f y := by
  classical
  have hdir : ∀ a b : Vertex, (a.1-b.1).natAbs+(a.2-b.2).natAbs ≤ 1 →
      f b-f a=label B S a b := by
    intro a b hab
    by_cases he : a=b
    · subst b;simp only [sub_self,label];split_ifs <;> norm_num; decide
    · have hn : (a.1-b.1).natAbs+(a.2-b.2).natAbs=1 := by
        by_contra hh
        have h1 := Int.natAbs_eq_zero.mp (show (a.1-b.1).natAbs=0 by omega)
        have h2 := Int.natAbs_eq_zero.mp (show (a.2-b.2).natAbs=0 by omega)
        exact he (Prod.ext (by omega) (by omega))
      exact hf a b hn
  let z : Vertex := (y.1,x.2)
  have h1 := hdir x z (by change (x.1-y.1).natAbs+(x.2-x.2).natAbs ≤ 1;simpa using hxy.2.1)
  have h2 := hdir z y (by change (y.1-y.1).natAbs+(x.2-y.2).natAbs ≤ 1;simpa using hxy.2.2)
  have hxs : x∉S := fun h => (hS h).1 hx
  have hys : y∉S := fun h => (hS h).1 hy
  have hl : label B S x z+label B S z y=0 := by
    simp only [label,hx,hy,hxs,hys,ite_true,ite_false]
    split_ifs <;> norm_num <;> decide
  have hh : f y-f x=0 := by
    calc
      _ = (f z-f x)+(f y-f z) := by abel
      _ = label B S x z+label B S z y := by rw [h1,h2]
      _ = 0 := hl
  exact (sub_eq_zero.mp hh).symm

lemma star_subcut_complete (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected)
    (S : Set Vertex) (hS : S ⊆ rim B) (hSne : S.Nonempty)
    (hclosed : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → (x∈S ↔ y∈S)) :
    ∀ b∈B, ∀ z∉B, grid.Adj b z → z∈S := by
  classical
  obtain ⟨f,hf⟩ := label_potential B hB S hS hclosed
  have hSc : S ⊆ (B:Set Vertex)ᶜ := fun _ h => (hS h).1
  have hci : ∀ x∈B, ∀ y∈B, f x=f y := by
    intro x hx y hy
    apply constant_of_connected (star.induce (B:Set Vertex)) hin (fun x => f x) _ ⟨x,hx⟩ ⟨y,hy⟩
    intro a b hab
    exact potential_const_star B S hS f hf a.property b.property hab
  have hco : ∀ x∉B, ∀ y∉B, f x=f y := by
    intro x hx y hy
    apply constant_of_connected (grid.induce ((B:Set Vertex)ᶜ)) hout (fun x => f x) _ ⟨x,hx⟩ ⟨y,hy⟩
    intro a b hab
    have hh := hf a b hab
    rw [label_same B S hSc (iff_of_false a.property b.property)] at hh
    exact (sub_eq_zero.mp hh).symm
  obtain ⟨b,hb,z,hz,hbz⟩ := boundary_in_set B S hS hSne hclosed
  have hzb := (hS hz).1
  have hbase : f z-f b=1 := by simpa [label,hb,hzb,hz] using hf b z hbz
  intro b' hb' z' hz' h'
  have he : label B S b' z'=1 := by
    rw [← hf b' z' h',← hci b hb b' hb',← hco z hzb z' hz']
    exact hbase
  by_contra hnot
  simp [label,hb',hz',hnot] at he

lemma star_rim_preconnected (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected) :
    (grid.induce (rim B)).Preconnected := by
  intro x y
  let S : Set Vertex := {z | ∃ hz : z∈rim B,
    (grid.induce (rim B)).Reachable x ⟨z,hz⟩}
  have hS : S ⊆ rim B := fun _ h => h.choose
  have hSne : S.Nonempty := ⟨x,x.property,SimpleGraph.Reachable.rfl⟩
  have hclosed : ∀ a∈rim B, ∀ b∈rim B, grid.Adj a b → (a∈S ↔ b∈S) := by
    intro a ha b hb hab
    constructor
    · rintro ⟨ha',hxa⟩
      exact ⟨hb,hxa.trans (SimpleGraph.Adj.reachable (G := grid.induce (rim B)) hab)⟩
    · rintro ⟨hb',hxb⟩
      exact ⟨ha,hxb.trans (SimpleGraph.Adj.reachable (G := grid.induce (rim B)) hab.symm)⟩
  have hboundary := star_subcut_complete B hB hin hout S hS hSne hclosed
  have hy : y.val∈S := by
    by_contra hy
    let T : Set Vertex := rim B \ S
    have hT : T ⊆ rim B := fun _ h => h.1
    have hTne : T.Nonempty := ⟨y,y.property,hy⟩
    have hTclosed : ∀ a∈rim B, ∀ b∈rim B, grid.Adj a b → (a∈T ↔ b∈T) := by
      intro a ha b hb hab
      simp only [T,Set.mem_sdiff,ha,hb,true_and]
      exact not_congr (hclosed a ha b hb hab)
    obtain ⟨b,hb,z,hz,hbz⟩ := boundary_in_set B T hT hTne hTclosed
    exact hz.2 (hboundary b hb z hz.1.1 hbz)
  exact hy.choose_spec

theorem star_rim_paths (B : Finset Vertex) (hB : B.Nonempty)
    (hconn : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected) :
    ∀ x ∈ rim B, ∀ y ∈ rim B,
      ∃ p : grid.Walk x y, (∀ z ∈ p.support, z ∈ rim B) ∧ p.length ≤ 8*B.card := by
  classical
  intro x hx y hy
  obtain ⟨R,hR,hRc⟩ := rim_finite_bound B
  obtain ⟨w,hw⟩ := (star_rim_preconnected B hB hconn hout ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
  let inc : grid.induce (rim B) →g grid := ⟨Subtype.val,fun h => h⟩
  let p := w.map inc
  have hp : p.IsPath := hw.map (by intro a b h;exact Subtype.ext h)
  have hsup : ∀ z∈p.support, z∈rim B := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
    exact q.property
  refine ⟨p,hsup,?_⟩
  have hcard : p.support.toFinset.card ≤ R.card := Finset.card_le_card (by
    intro z hz
    have hh := hsup z (List.mem_toFinset.mp hz)
    rwa [← hR] at hh)
  rw [List.toFinset_card_of_nodup hp.support_nodup,SimpleGraph.Walk.length_support] at hcard
  omega

end SparseHoles

end

end OAI
