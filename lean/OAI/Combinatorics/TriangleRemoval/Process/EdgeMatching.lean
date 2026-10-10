import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def EdgeMatching {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧ ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e f

namespace EdgeMatching
variable {V : Type*} [DecidableEq V] {E : Finset (Finset V)}

lemma singleton (e : Finset V) (he : e.card = 2) : EdgeMatching {e} := by
  constructor
  · intro f hf
    simpa only [Finset.mem_singleton.mp hf] using he
  · intro f hf g hg hfg
    exact False.elim (hfg ((Finset.mem_singleton.mp hf).trans (Finset.mem_singleton.mp hg).symm))

lemma pair (e f : Finset V) (he : e.card = 2) (hf : f.card = 2)
    (hd : Disjoint e f) : EdgeMatching {e,f} := by
  constructor
  · intro g hg
    rcases Finset.mem_insert.mp hg with h | h
    · simpa only [h] using he
    · simpa only [Finset.mem_singleton.mp h] using hf
  · intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hd
    · exact hd.symm
    · exact False.elim (hab rfl)

lemma unique_neighbor (hE : EdgeMatching E) {x y z : V}
    (hx : {x,z} ∈ E) (hy : {y,z} ∈ E) : x = y := by
  have hxz : x ≠ z := by
    intro he
    have hc := hE.1 _ hx
    simp [he] at hc
  have he : ({x,z} : Finset V) = {y,z} := by
    by_contra hn
    exact (Finset.disjoint_left.mp (hE.2 _ hx _ hy hn) (show z ∈ ({x,z} : Finset V) by simp)
      (show z ∈ ({y,z} : Finset V) by simp))
  have hm : x ∈ ({y,z} : Finset V) := he ▸ (by simp)
  exact (Finset.mem_insert.mp hm).resolve_right (by simpa using hxz)

end EdgeMatching

noncomputable def matchingSeed {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R}) : BirthGraph N where
  older v := Finset.univ.filter (fun u => v.val < R ∧ u < v ∧ {label u,label v} ∈ E)
  older_lt := by
    intro v u hu
    exact (Finset.mem_filter.mp hu).2.2.1
  older_card := by
    intro v
    apply (Finset.card_le_one.mpr ?_).trans (show 1 ≤ 2 by omega)
    intro x hx y hy
    obtain ⟨_,hv,hxv,hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨_,_,hyv,hye⟩ := Finset.mem_filter.mp hy
    apply hi (show x.val < R by exact lt_trans hxv hv)
      (show y.val < R by exact lt_trans hyv hv)
    exact hE.unique_neighbor hxe hye

section MatchingSeed
variable {V : Type*} [DecidableEq V] {N R : ℕ}
variable (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
variable (hi : Set.InjOn label {v | v.val < R})

@[simp] lemma matchingSeed_mem_older (v u : Fin N) :
    u ∈ (matchingSeed label E hE hi).older v ↔
      v.val < R ∧ u < v ∧ {label u,label v} ∈ E := by
  simp only [matchingSeed,Finset.mem_filter,Finset.mem_univ,true_and]

lemma matchingSeed_small (v : Fin N) : ((matchingSeed label E hE hi).older v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hv,hxv,hxe⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hx
  obtain ⟨_,hyv,hye⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hy
  exact hi (show x.val < R by exact lt_trans hxv hv)
      (show y.val < R by exact lt_trans hyv hv) (hE.unique_neighbor hxe hye)

lemma matchingSeed_root (v u : Fin N) (hu : u ∈ (matchingSeed label E hE hi).older v) :
    u.val < R := by
  obtain ⟨hv,huv,_⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hu
  exact lt_trans huv hv

lemma matchingSeed_labels (G : SimpleGraph V)
    (hl : ∀ e ∈ E, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y)
    (v u : Fin N) (hu : u ∈ (matchingSeed label E hE hi).older v) :
    G.Adj (label u) (label v) := by
  obtain ⟨hv,huv,he⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hu
  have hne : label u ≠ label v := fun h => (ne_of_lt huv) (hi (show u.val < R from lt_trans huv hv) hv h)
  exact hl _ he _ (by simp) _ (by simp) hne

lemma matchingSeed_covers
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x)
    (e : Finset V) (he : e ∈ E) :
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧
      (matchingSeed label E hE hi).graph.Adj x y ∧ e = {label x,label y} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (hE.1 e he)
  obtain ⟨x,hx,hxa⟩ := hc _ he a (by simp)
  obtain ⟨y,hy,hyb⟩ := hc _ he b (by simp)
  have hxy : x ≠ y := fun heq => hab ((hxa.symm.trans (congrArg label heq)).trans hyb)
  refine ⟨x,y,hx,hy,?_,by rw [hxa,hyb]⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact Or.inl ((matchingSeed_mem_older _ _ _ _ _ _).mpr ⟨hy,hlt,by simpa [hxa,hyb] using he⟩)
  · exact Or.inr ((matchingSeed_mem_older _ _ _ _ _ _).mpr ⟨hx,hgt,by
      simpa [hxa,hyb,Finset.pair_comm] using he⟩)

end MatchingSeed
end SharpTerminalLeave

end

end OAI
