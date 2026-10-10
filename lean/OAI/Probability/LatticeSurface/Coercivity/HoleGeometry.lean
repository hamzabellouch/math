import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridClosedLabels

end GridClosedLabels

namespace GridClosedLabels

end GridClosedLabels

namespace SparseHoles

abbrev Vertex := ℤ × ℤ

def grid : SimpleGraph Vertex where
  Adj x y := (x.1-y.1).natAbs+(x.2-y.2).natAbs=1
  symm := ⟨by
    intro x y h
    have hab (a b : ℤ) : (a-b).natAbs=(b-a).natAbs := by
      rw [← Int.natAbs_neg (a-b),neg_sub]
    rwa [hab y.1 x.1,hab y.2 x.2]⟩
  loopless := ⟨by intro x;simp⟩

def rim (B : Finset Vertex) : Set Vertex := {x | x ∉ B ∧
  ∃ y ∈ B, (x.1-y.1).natAbs ≤ 1 ∧ (x.2-y.2).natAbs ≤ 1}

lemma abs_small {a b : ℤ} (h : -1 ≤ a-b ∧ a-b ≤ 1) : (a-b).natAbs ≤ 1 := by
  have hh : |a-b| ≤ (1:ℤ) := abs_le.mpr h
  exact_mod_cast (show ((a-b).natAbs:ℤ) ≤ 1 by simpa using hh)

lemma adj_cases {x y : Vertex} (h : grid.Adj x y) :
    y=(x.1+1,x.2) ∨ y=(x.1-1,x.2) ∨ y=(x.1,x.2+1) ∨ y=(x.1,x.2-1) := by
  change (x.1-y.1).natAbs+(x.2-y.2).natAbs=1 at h
  have hx : (x.1-y.1).natAbs=0 ∨ (x.1-y.1).natAbs=1 := by omega
  rcases hx with hx|hx
  · have he := Int.natAbs_eq_iff.mp hx
    have hy : (x.2-y.2).natAbs=1 := by omega
    rcases Int.natAbs_eq_iff.mp hy with hy|hy
    · right;right;right;ext <;> simp_all <;> omega
    · right;right;left;ext <;> simp_all <;> omega
  · have he := Int.natAbs_eq_iff.mp (show (x.2-y.2).natAbs=0 by omega)
    rcases Int.natAbs_eq_iff.mp hx with hx|hx
    · right;left;ext <;> simp_all <;> omega
    · left;ext <;> simp_all <;> omega

lemma adj_right (x y : ℤ) : grid.Adj (x,y) (x+1,y) := by
  change (x-(x+1)).natAbs+(y-y).natAbs=1
  simp

lemma adj_up (x y : ℤ) : grid.Adj (x,y) (x,y+1) := by
  change (x-x).natAbs+(y-(y+1)).natAbs=1
  simp

noncomputable def label (B : Finset Vertex) (S : Set Vertex) (x y : Vertex) : ZMod 2 := by
  classical
  exact (if x∈B then (if y∈S then 1 else 0) else 0) +
  (if y∈B then (if x∈S then 1 else 0) else 0)

lemma label_symm (B : Finset Vertex) (S : Set Vertex) (x y : Vertex) :
    label B S x y=label B S y x := by simp [label,add_comm]

lemma label_same (B : Finset Vertex) (S : Set Vertex) (hS : S ⊆ (B:Set Vertex)ᶜ)
    {x y : Vertex} (h : (x∈B ↔ y∈B)) : label B S x y=0 := by
  classical
  by_cases hx : x∈B
  · have hy := h.mp hx
    have hxs : x∉S := fun hs => hS hs hx
    have hys : y∉S := fun hs => hS hs hy
    simp [label,hx,hy,hxs,hys]
  · have hy : y∉B := fun hy => hx (h.mpr hy)
    simp [label,hx,hy]

lemma square_rim {B : Finset Vertex} {i j : ℤ} (hb :
    (i,j)∈B ∨ (i+1,j)∈B ∨ (i+1,j+1)∈B ∨ (i,j+1)∈B)
    {x : Vertex} (hx : x∉B) (hi : i ≤ x.1 ∧ x.1 ≤ i+1)
    (hj : j ≤ x.2 ∧ x.2 ≤ j+1) : x∈rim B := by
  refine ⟨hx,?_⟩
  rcases hb with h|h|h|h
  · exact ⟨(i,j),h,abs_small (by omega),abs_small (by omega)⟩
  · exact ⟨(i+1,j),h,abs_small (by omega),abs_small (by omega)⟩
  · exact ⟨(i+1,j+1),h,abs_small (by omega),abs_small (by omega)⟩
  · exact ⟨(i,j+1),h,abs_small (by omega),abs_small (by omega)⟩

lemma label_closed (B : Finset Vertex) (S : Set Vertex) (hS : S ⊆ rim B)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → (x∈S ↔ y∈S)) (i j : ℤ) :
    label B S (i,j+1) (i+1,j+1)-label B S (i,j) (i+1,j) =
      label B S (i+1,j) (i+1,j+1)-label B S (i,j) (i,j+1) := by
  classical
  by_cases hb : (i,j)∈B ∨ (i+1,j)∈B ∨ (i+1,j+1)∈B ∨ (i,j+1)∈B
  · let s : Vertex → ZMod 2 := fun x => if x∈S then 1 else 0
    have hzero : ∀ x∈B, s x=0 := by
      intro x hx
      have hxs : x∉S := fun h => (hS h).1 hx
      simp [s,hxs]
    have heq : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → s x=s y := by
      intro x hx y hy hxy
      simp [s,hconn x hx y hy hxy]
    have hr0 : (i,j)∉B → (i,j)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr1 : (i+1,j)∉B → (i+1,j)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr2 : (i+1,j+1)∉B → (i+1,j+1)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hr3 : (i,j+1)∉B → (i,j+1)∈rim B := fun h => square_rim hb h (by simp) (by simp)
    have hh := GridClosedLabels.square_binary
      (decide ((i,j)∈B)) (decide ((i+1,j)∈B))
      (decide ((i+1,j+1)∈B)) (decide ((i,j+1)∈B))
      (s (i,j)) (s (i+1,j)) (s (i+1,j+1)) (s (i,j+1))
      (by simpa using hzero (i,j)) (by simpa using hzero (i+1,j))
      (by simpa using hzero (i+1,j+1)) (by simpa using hzero (i,j+1))
      (by simpa using fun h0 h1 => heq _ (hr0 h0) _ (hr1 h1) (adj_right i j))
      (by simpa using fun h1 h2 => heq _ (hr1 h1) _ (hr2 h2) (adj_up (i+1) j))
      (by simpa using fun h2 h3 => heq _ (hr2 h2) _ (hr3 h3) (adj_right i (j+1)).symm)
      (by simpa using fun h3 h0 => heq _ (hr3 h3) _ (hr0 h0) (adj_up i j).symm)
    simpa [label,s] using hh
  · push Not at hb
    simp [label,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]

lemma label_potential (B : Finset Vertex) (hB : B.Nonempty) (S : Set Vertex)
    (hS : S ⊆ rim B)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → (x∈S ↔ y∈S)) :
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
  have hface : ∀ x y, H x (y+1)-H x y=V (x+1) y-V x y := label_closed B S hS hconn
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

lemma boundary_in_set (B : Finset Vertex) (S : Set Vertex)
    (hS : S ⊆ rim B) (hSne : S.Nonempty)
    (hconn : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → (x∈S ↔ y∈S)) :
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
      have hzs := (hconn x (hS hx) z hzr hxz).mp hx
      exact ⟨y,hy,z,hzs,hzy.symm⟩

lemma constant_of_connected {V A : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (f : V → A) (hf : ∀ x y, G.Adj x y → f x=f y) (x y : V) : f x=f y := by
  obtain ⟨p⟩ := hG x y
  induction p with
  | nil => rfl
  | cons h p ih => exact (hf _ _ h).trans ih

lemma subcut_complete (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (grid.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected)
    (S : Set Vertex) (hS : S ⊆ rim B) (hSne : S.Nonempty)
    (hclosed : ∀ x∈rim B, ∀ y∈rim B, grid.Adj x y → (x∈S ↔ y∈S)) :
    ∀ b∈B, ∀ z∉B, grid.Adj b z → z∈S := by
  classical
  obtain ⟨f,hf⟩ := label_potential B hB S hS hclosed
  have hSc : S ⊆ (B:Set Vertex)ᶜ := fun _ h => (hS h).1
  have hci : ∀ x∈B, ∀ y∈B, f x=f y := by
    intro x hx y hy
    apply constant_of_connected (grid.induce (B:Set Vertex)) hin (fun x => f x) _ ⟨x,hx⟩ ⟨y,hy⟩
    intro a b hab
    have hh := hf a b hab
    rw [label_same B S hSc (iff_of_true a.property b.property)] at hh
    exact (sub_eq_zero.mp hh).symm
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

lemma rim_preconnected (B : Finset Vertex) (hB : B.Nonempty)
    (hin : (grid.induce (B:Set Vertex)).Connected)
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
  have hboundary := subcut_complete B hB hin hout S hS hSne hclosed
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

def offsets8 : Finset Vertex :=
  (({-1,0,1}:Finset ℤ) ×ˢ ({-1,0,1}:Finset ℤ)).erase (0,0)

lemma offsets8_card : offsets8.card=8 := by decide

lemma rim_finite_bound (B : Finset Vertex) :
    ∃ R : Finset Vertex, (R:Set Vertex)=rim B ∧ R.card ≤ 8*B.card := by
  classical
  let T : Finset Vertex := B.biUnion fun y => offsets8.image (fun d => y+d)
  have hsubset : ∀ x∈rim B, x∈T := by
    rintro x ⟨hx,y,hy,h1,h2⟩
    have hne : x-y≠(0,0) := by
      intro h
      have he : x=y := by simpa using sub_eq_zero.mp h
      exact hx (he ▸ hy)
    have hsmall {a : ℤ} (h : a.natAbs ≤ 1) : a∈({-1,0,1}:Finset ℤ) := by
      have hh : a.natAbs=0 ∨ a.natAbs=1 := by omega
      rcases hh with hh|hh
      · have he := Int.natAbs_eq_zero.mp hh;simp [he]
      · rcases Int.natAbs_eq_iff.mp hh with hh|hh <;> simp [hh]
    have hd : x-y∈offsets8 := by
      simp only [offsets8,Finset.mem_erase,Finset.mem_product]
      exact ⟨hne,hsmall h1,hsmall h2⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y,hy,Finset.mem_image.mpr ⟨x-y,hd,?_⟩⟩
    abel
  refine ⟨T.filter (fun x => x∈rim B),?_,?_⟩
  · ext x;simp only [Finset.mem_coe,Finset.mem_filter];exact ⟨And.right,fun h => ⟨hsubset x h,h⟩⟩
  · calc
      _ ≤ T.card := Finset.card_filter_le _ _
      _ ≤ ∑ _y∈B, 8 := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
        intro y hy
        exact (Finset.card_image_le).trans_eq offsets8_card
      _ = 8*B.card := by simp [mul_comm]

theorem rim_paths (B : Finset Vertex) (hB : B.Nonempty)
    (hconn : (grid.induce (B:Set Vertex)).Connected)
    (hout : (grid.induce ((B:Set Vertex)ᶜ)).Connected) :
    ∀ x ∈ rim B, ∀ y ∈ rim B,
      ∃ p : grid.Walk x y, (∀ z ∈ p.support, z ∈ rim B) ∧ p.length ≤ 8*B.card := by
  classical
  intro x hx y hy
  obtain ⟨R,hR,hRc⟩ := rim_finite_bound B
  obtain ⟨w,hw⟩ := (rim_preconnected B hB hconn hout ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
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
