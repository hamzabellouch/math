import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleStar

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

def incident (B : Finset Vertex) (x : Vertex) : Prop := ∃ b∈B, grid.Adj b x

def rimNet (B : Finset Vertex) : SimpleGraph Vertex where
  Adj x y := grid.Adj x y ∧ (incident B x ∨ incident B y)
  symm := ⟨by intro x y h;exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro x h;exact grid.irrefl h.1⟩

lemma net_label_closed (B : Finset Vertex) (S : Set Vertex) (hS : S ⊆ rim B)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, (rimNet B).Adj x y → (x∈S ↔ y∈S)) (i j : ℤ) :
    label B S (i,j+1) (i+1,j+1)-label B S (i,j) (i+1,j) =
      label B S (i+1,j) (i+1,j+1)-label B S (i,j) (i,j+1) := by
  classical
  by_cases hb : (i,j)∈B ∨ (i+1,j)∈B ∨ (i+1,j+1)∈B ∨ (i,j+1)∈B
  · let s : Vertex → ZMod 2 := fun x => if x∈S then 1 else 0
    have hzero : ∀ x∈B, s x=0 := by
      intro x hx
      have hxs : x∉S := fun h => (hS h).1 hx
      simp [s,hxs]
    have heq : ∀ x∈rim B, ∀ y∈rim B, (rimNet B).Adj x y → s x=s y := by
      intro x hx y hy hxy
      simp [s,hconn x hx y hy hxy]
    have hr0 : (i,j)∉B → (i,j)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr1 : (i+1,j)∉B → (i+1,j)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr2 : (i+1,j+1)∉B → (i+1,j+1)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr3 : (i,j+1)∉B → (i,j+1)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hn01 (h0 : (i,j)∉B) (h1 : (i+1,j)∉B) : (rimNet B).Adj (i,j) (i+1,j) := by
      refine ⟨adj_right i j,?_⟩
      rcases hb with h|h|h|h
      · exact (h0 h).elim
      · exact (h1 h).elim
      · exact Or.inr ⟨(i+1,j+1),h,(adj_up (i+1) j).symm⟩
      · exact Or.inl ⟨(i,j+1),h,(adj_up i j).symm⟩
    have hn12 (h1 : (i+1,j)∉B) (h2 : (i+1,j+1)∉B) : (rimNet B).Adj (i+1,j) (i+1,j+1) := by
      refine ⟨adj_up (i+1) j,?_⟩
      rcases hb with h|h|h|h
      · exact Or.inl ⟨(i,j),h,adj_right i j⟩
      · exact (h1 h).elim
      · exact (h2 h).elim
      · exact Or.inr ⟨(i,j+1),h,adj_right i (j+1)⟩
    have hn23 (h2 : (i+1,j+1)∉B) (h3 : (i,j+1)∉B) : (rimNet B).Adj (i+1,j+1) (i,j+1) := by
      refine ⟨(adj_right i (j+1)).symm,?_⟩
      rcases hb with h|h|h|h
      · exact Or.inr ⟨(i,j),h,adj_up i j⟩
      · exact Or.inl ⟨(i+1,j),h,adj_up (i+1) j⟩
      · exact (h2 h).elim
      · exact (h3 h).elim
    have hn30 (h3 : (i,j+1)∉B) (h0 : (i,j)∉B) : (rimNet B).Adj (i,j+1) (i,j) := by
      refine ⟨(adj_up i j).symm,?_⟩
      rcases hb with h|h|h|h
      · exact (h0 h).elim
      · exact Or.inr ⟨(i+1,j),h,(adj_right i j).symm⟩
      · exact Or.inl ⟨(i+1,j+1),h,(adj_right i (j+1)).symm⟩
      · exact (h3 h).elim
    have hh := GridClosedLabels.square_binary
      (decide ((i,j)∈B)) (decide ((i+1,j)∈B))
      (decide ((i+1,j+1)∈B)) (decide ((i,j+1)∈B))
      (s (i,j)) (s (i+1,j)) (s (i+1,j+1)) (s (i,j+1))
      (by simpa using hzero (i,j)) (by simpa using hzero (i+1,j))
      (by simpa using hzero (i+1,j+1)) (by simpa using hzero (i,j+1))
      (by simpa using fun h0 h1 => heq _ (hr0 h0) _ (hr1 h1) (hn01 h0 h1))
      (by simpa using fun h1 h2 => heq _ (hr1 h1) _ (hr2 h2) (hn12 h1 h2))
      (by simpa using fun h2 h3 => heq _ (hr2 h2) _ (hr3 h3) (hn23 h2 h3))
      (by simpa using fun h3 h0 => heq _ (hr3 h3) _ (hr0 h0) (hn30 h3 h0))
    simpa [label,s] using hh
  · push Not at hb
    simp [label,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]

lemma net_label_potential (B : Finset Vertex) (hB : B.Nonempty) (S : Set Vertex)
    (hS : S ⊆ rim B)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, (rimNet B).Adj x y → (x∈S ↔ y∈S)) :
    ∃ f : Vertex → ZMod 2, ∀ x y, grid.Adj x y → f y-f x=label B S x y := by
  classical
  let a : ℤ := (B.image Prod.fst).min' (hB.image _) - 2
  have hbound : ∀ b∈B, a+1 < b.1 := by
    intro b hb
    have hh := Finset.min'_le (B.image Prod.fst) b.1 (Finset.mem_image_of_mem Prod.fst hb)
    dsimp [a]
    omega
  let H : ℤ → ℤ → ZMod 2 := fun x y => label B S (x,y) (x+1,y)
  let V : ℤ → ℤ → ZMod 2 := fun x y => label B S (x,y) (x,y+1)
  have hH : ∀ x<a, ∀ y, H x y=0 := by
    intro x hx y
    have h0 : (x,y)∉B := by intro h;have := hbound _ h;dsimp at this;omega
    have h1 : (x+1,y)∉B := by intro h;have := hbound _ h;dsimp at this;omega
    simp [H,label,h0,h1]
  have hV : ∀ x≤a, ∀ y, V x y=0 := by
    intro x hx y
    have h0 : (x,y)∉B := by intro h;have := hbound _ h;dsimp at this;omega
    have h1 : (x,y+1)∉B := by intro h;have := hbound _ h;dsimp at this;omega
    simp [V,label,h0,h1]
  have hface : ∀ x y, H x (y+1)-H x y=V (x+1) y-V x y := net_label_closed B S hS hconn
  let f : Vertex → ZMod 2 := fun z => GridClosedLabels.rayPotential H a z.1 z.2
  have hr : ∀ x y, f (x+1,y)-f (x,y)=label B S (x,y) (x+1,y) := by
    intro x y
    exact GridClosedLabels.ray_horizontal H a x y hH
  have hu : ∀ x y, f (x,y+1)-f (x,y)=label B S (x,y) (x,y+1) := by
    intro x y
    exact GridClosedLabels.ray_vertical H V a x y hV hface
  refine ⟨f,?_⟩
  intro x y hxy
  rcases adj_cases hxy with hy|hy|hy|hy
  · subst y;exact hr x.1 x.2
  · subst y
    have hh := hr (x.1-1) x.2
    have hh' := congrArg Neg.neg hh
    simpa only [sub_add_cancel,Prod.eta,neg_sub,ZMod.neg_eq_self_mod_two,label_symm B S x] using hh'
  · subst y;exact hu x.1 x.2
  · subst y
    have hh := hu x.1 (x.2-1)
    have hh' := congrArg Neg.neg hh
    simpa only [sub_add_cancel,Prod.eta,neg_sub,ZMod.neg_eq_self_mod_two,label_symm B S x] using hh'

lemma net_boundary_in_set (B : Finset Vertex) (S : Set Vertex)
    (hS : S ⊆ rim B) (hSne : S.Nonempty)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, (rimNet B).Adj x y → (x∈S ↔ y∈S)) :
    ∃ b∈B, ∃ z∈S, grid.Adj b z := by
  obtain ⟨x,hx⟩ := hSne
  obtain ⟨hxb,y,hy,hdx,hdy⟩ := hS hx
  have hn : (x.1-y.1).natAbs+(x.2-y.2).natAbs≠0 := by
    intro h
    have h1 : x.1=y.1 := by have := Int.natAbs_eq_zero.mp (show (x.1-y.1).natAbs=0 by omega);omega
    have h2 : x.2=y.2 := by have := Int.natAbs_eq_zero.mp (show (x.2-y.2).natAbs=0 by omega);omega
    have he : x=y := Prod.ext h1 h2
    exact hxb (he ▸ hy)
  by_cases hsum : (x.1-y.1).natAbs+(x.2-y.2).natAbs=1
  · exact ⟨y,hy,x,hx,(show grid.Adj x y from hsum).symm⟩
  · have h1 : (x.1-y.1).natAbs=1 := by omega
    have h2 : (x.2-y.2).natAbs=1 := by omega
    let z : Vertex := (x.1,y.2)
    have hxz : grid.Adj x z := by change (x.1-x.1).natAbs+(x.2-y.2).natAbs=1;simp [h2]
    have hzy : grid.Adj z y := by change (x.1-y.1).natAbs+(y.2-y.2).natAbs=1;simp [h1]
    by_cases hz : z∈B
    · exact ⟨z,hz,x,hx,hxz.symm⟩
    · have hzr : z∈rim B := ⟨hz,y,hy,by simpa [z] using hdx,by simp [z]⟩
      have hzs := (hconn x (hS hx) z hzr ⟨hxz,Or.inr ⟨y,hy,hzy.symm⟩⟩).mp hx
      exact ⟨y,hy,z,hzs,hzy.symm⟩

lemma net_star_subcut_complete (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected)
    (S : Set Vertex) (hS : S ⊆ rim B) (hSne : S.Nonempty)
    (hclosed : ∀ x∈rim B, ∀ y∈rim B, (rimNet B).Adj x y → (x∈S ↔ y∈S)) :
    ∀ b∈B, ∀ z∉B, grid.Adj b z → z∈S := by
  classical
  obtain ⟨f,hf⟩ := net_label_potential B hB S hS hclosed
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
  obtain ⟨b,hb,z,hz,hbz⟩ := net_boundary_in_set B S hS hSne hclosed
  have hzb := (hS hz).1
  have hbase : f z-f b=1 := by simpa [label,hb,hzb,hz] using hf b z hbz
  intro b' hb' z' hz' h'
  have he : label B S b' z'=1 := by
    rw [← hf b' z' h',← hci b hb b' hb',← hco z hzb z' hz']
    exact hbase
  by_contra hnot
  simp [label,hb',hz',hnot] at he

lemma net_star_rim_preconnected (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected) :
    ((rimNet B).induce (rim B)).Preconnected := by
  intro x y
  let S : Set Vertex := {z | ∃ hz : z∈rim B,
    ((rimNet B).induce (rim B)).Reachable x ⟨z,hz⟩}
  have hS : S ⊆ rim B := fun _ h => h.choose
  have hSne : S.Nonempty := ⟨x,x.property,SimpleGraph.Reachable.rfl⟩
  have hclosed : ∀ a∈rim B, ∀ b∈rim B, (rimNet B).Adj a b → (a∈S ↔ b∈S) := by
    intro a ha b hb hab
    constructor
    · rintro ⟨ha',hxa⟩
      exact ⟨hb,hxa.trans (SimpleGraph.Adj.reachable (G := (rimNet B).induce (rim B)) hab)⟩
    · rintro ⟨hb',hxb⟩
      exact ⟨ha,hxb.trans (SimpleGraph.Adj.reachable (G := (rimNet B).induce (rim B)) hab.symm)⟩
  have hboundary := net_star_subcut_complete B hB hin hout S hS hSne hclosed
  have hy : y.val∈S := by
    by_contra hy
    let T : Set Vertex := rim B \ S
    have hT : T ⊆ rim B := fun _ h => h.1
    have hTne : T.Nonempty := ⟨y,y.property,hy⟩
    have hTclosed : ∀ a∈rim B, ∀ b∈rim B, (rimNet B).Adj a b → (a∈T ↔ b∈T) := by
      intro a ha b hb hab
      simp only [T,Set.mem_sdiff,ha,hb,true_and]
      exact not_congr (hclosed a ha b hb hab)
    obtain ⟨b,hb,z,hz,hbz⟩ := net_boundary_in_set B T hT hTne hTclosed
    exact hz.2 (hboundary b hb z hz.1.1 hbz)
  exact hy.choose_spec

theorem incident_rim_paths (B : Finset Vertex) (hB : B.Nonempty)
    (hconn : (star.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected) :
    ∀ x ∈ rim B, ∀ y ∈ rim B,
      ∃ p : (rimNet B).Walk x y, (∀ z ∈ p.support, z ∈ rim B) ∧ p.length ≤ 8*B.card := by
  classical
  intro x hx y hy
  obtain ⟨R,hR,hRc⟩ := rim_finite_bound B
  obtain ⟨w,hw⟩ := (net_star_rim_preconnected B hB hconn hout ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
  let inc : (rimNet B).induce (rim B) →g rimNet B := ⟨Subtype.val,fun h => h⟩
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
