import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PartitionGeometry
import OAI.Combinatorics.ThinTrees.Restriction

namespace OAI

/-! Partition local connectivity. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

def split (p : Setoid V) (S : Finset V) : Setoid V := p ⊓ Setoid.ker (fun v => v ∈ S)

omit [Fintype V] in
lemma split_iff (p : Setoid V) (S : Finset V) (a b : V) :
    split p S a b ↔ p a b ∧ (a ∈ S ↔ b ∈ S) := by
  change (p a b ∧ (a ∈ S)=(b ∈ S)) ↔ _
  simp only [eq_iff_iff]

lemma split_strict {p : Setoid V} {v : V} {S : Finset V}
    (hne : S.Nonempty) (hS : S ⊂ block p v) : split p S < p := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  obtain ⟨a,ha⟩ := hne
  have hbex : ∃b ∈ block p v, b ∉ S := by
    by_contra h
    push Not at h
    exact hS.not_ge h
  obtain ⟨b,hb,hbn⟩ := hbex
  have hab : p a b := block_block p (hS.subset ha) hb
  have hsplit : split p S a b := Eq.mpr (congrArg (fun q : Setoid V => q a b) he) hab
  exact hbn (((split_iff p S a b).mp hsplit).2.mp ha)

variable {n m : ℕ}

lemma crossing_split (G : MultiGraph n m) (p : Setoid (Fin n)) (v : Fin n)
    {S : Finset (Fin n)} (hS : S ⊆ block p v) :
    crossing G (split p S)=crossing G p ∪ G.cut (G.inducedEdges (block p v)) S := by
  ext e
  simp only [mem_crossing,split_iff,mem_union,MultiGraph.cut,mem_filter,mem_inducedEdges]
  have hl : G.left e ∈ S → G.left e ∈ block p v := fun h => hS h
  have hr : G.right e ∈ S → G.right e ∈ block p v := fun h => hS h
  have hlr : p (G.left e) (G.right e) → G.left e ∈ block p v → G.right e ∈ block p v := by
    intro he hleft
    exact (mem_block _ _ _).mpr (p.trans ((mem_block _ _ _).mp hleft) he)
  have hrl : p (G.left e) (G.right e) → G.right e ∈ block p v → G.left e ∈ block p v := by
    intro he hright
    exact (mem_block _ _ _).mpr (p.trans ((mem_block _ _ _).mp hright) (p.symm he))
  by_cases hp : p (G.left e) (G.right e) <;>
    by_cases hls : G.left e ∈ S <;> by_cases hrs : G.right e ∈ S <;> simp_all

lemma crossing_split_disjoint (G : MultiGraph n m) (p : Setoid (Fin n)) (v : Fin n)
    (S : Finset (Fin n)) :
    Disjoint (crossing G p) (G.cut (G.inducedEdges (block p v)) S) := by
  apply disjoint_left.mpr
  intro e hp hi
  have he := (mem_inducedEdges _ _ _).mp (mem_filter.mp hi).1
  exact (mem_crossing G p e).mp hp (block_block p he.1 he.2)

lemma capacity_split (G : MultiGraph n m) (w : Fin m → ℝ) (p : Setoid (Fin n)) (v : Fin n)
    {S : Finset (Fin n)} (hS : S ⊆ block p v) :
    capacity G.left G.right w (split p S)=capacity G.left G.right w p+
      ∑e ∈ G.cut (G.inducedEdges (block p v)) S, w e := by
  rw [capacity_eq_sum,capacity_eq_sum,crossing_split G p v hS,
    sum_union (crossing_split_disjoint G p v S)]

lemma split_capacity_lower (G : MultiGraph n m) (w : Fin m → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinv : ∀p, 0 ≤ slack G.left G.right w Q p)
    {p : Setoid (Fin n)} (hp : slack G.left G.right w Q p ≤ 1) (v : Fin n)
    {S : Finset (Fin n)} (hne : S.Nonempty) (hS : S ⊂ block p v) :
    Q-1 ≤ ∑e ∈ G.cut (G.inducedEdges (block p v)) S, w e := by
  have hc : partCount p+1 ≤ partCount (split p S) :=
    partCount_strictAnti (split_strict hne hS)
  have hcR : (partCount p:ℝ)+1 ≤ partCount (split p S) := by exact_mod_cast hc
  have hi := hinv (split p S)
  dsimp only [slack] at hi hp
  rw [capacity_split G w p v hS.subset] at hi
  have hh := mul_le_mul_of_nonneg_left hcR hQ
  nlinarith only [hi,hp,hh]

def active (u : Fin m → ℝ) : Finset (Fin m) := univ.filter (fun e => 0 < u e)

@[simp] lemma mem_active (u : Fin m → ℝ) (e : Fin m) : e ∈ active u ↔ 0 < u e := by
  simp [active]

lemma capacity_active_upper (u : Fin m → ℝ) (_hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (F : Finset (Fin m)) :
    (∑e ∈ F, (u e+κ)) ≤ ((F ∩ active u).card:ℝ)+κ*m := by
  have hpoint (e : Fin m) : u e ≤ if e ∈ active u then (1:ℝ) else 0 := by
    split_ifs with he
    · exact hu1 e
    · have he' : ¬0 < u e := by simpa using he
      exact le_of_not_gt he'
  have hsum := sum_le_sum (fun e (_ : e ∈ F) => hpoint e)
  have he : (∑e ∈ F, if e ∈ active u then (1:ℝ) else 0)=((F ∩ active u).card:ℝ) := by
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    congr 1
  rw [he] at hsum
  have hcard : (F.card:ℝ) ≤ m := by
    exact_mod_cast (show F.card ≤ m by simpa only [Fintype.card_fin] using card_le_univ F)
  have hm := mul_le_mul_of_nonneg_left hcard hκ
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
  nlinarith only [hsum,hm]

lemma restrict_induced (G : MultiGraph n m) (F : Finset (Fin m)) (A : Finset (Fin n)) :
    liftEdges F ((G.restrict F).inducedEdges A)=G.inducedEdges A ∩ F := by
  ext e
  simp only [liftEdges,mem_map,mem_inter,mem_inducedEdges]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,embedding_mem F i⟩
  · rintro ⟨hi,he⟩
    obtain ⟨i,rfl⟩ := embedding_surj F he
    exact ⟨i,hi,rfl⟩

lemma restrict_internal_cut_card (G : MultiGraph n m) (F : Finset (Fin m))
    (A S : Finset (Fin n)) :
    ((G.restrict F).cut ((G.restrict F).inducedEdges A) S).card=
      (G.cut (G.inducedEdges A) S ∩ F).card := by
  rw [G.restrict_cut_card,restrict_induced]
  congr 1
  ext e
  simp only [MultiGraph.cut,mem_filter,mem_inter]
  tauto

theorem near_tight_locally_connected (G : MultiGraph n m) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {κ Q h : ℝ} (hκ : 0 ≤ κ) (hκm : κ*m < 1) (hQ : 0 ≤ Q) (hh : h ≤ Q-2)
    (hinv : ∀p, 0 ≤ slack G.left G.right (fun e => u e+κ) Q p)
    {p : Setoid (Fin n)} (hp : slack G.left G.right (fun e => u e+κ) Q p ≤ 1)
    {A : Finset (Fin n)} (hA : A ∈ parts p) :
    (G.restrict (active u)).EdgeConnectedReal A h := by
  obtain ⟨v,rfl⟩ := (mem_parts p A).mp hA
  intro S hne hS
  have hb := split_capacity_lower G (fun e => u e+κ) hQ hinv hp v hne hS
  have hu := capacity_active_upper u hu0 hu1 hκ (G.cut (G.inducedEdges (block p v)) S)
  rw [restrict_internal_cut_card]
  linarith only [hb,hu,hκm,hh]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
