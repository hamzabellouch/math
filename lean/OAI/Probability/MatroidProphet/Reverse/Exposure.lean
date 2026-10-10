import OAI.Probability.MatroidProphet.BatchReveal
import OAI.Probability.MatroidProphet.Reverse.Paths
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseLayer (α : Type*) where
  group : Finset α
  density : Set α
  state : Set α
  enabledAt : ℤ

noncomputable def layerNominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Set α :=
  densityEnabled M hE κ L.density L.enabledAt k A

noncomputable def layerBatch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) : Finset α :=
  L.group.filter (fun e => e ∈ L.state ∧ e ∉ layerNominal M hE κ k L A)

noncomputable def layerUpdate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) : Set α :=
  M.closure (layerNominal M hE κ k L A ∪ ((C : Set α) ∩ (L.group : Set α) ∩ L.state))

lemma layerUpdate_eq_batch (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C : Finset α) :
    layerUpdate M hE κ k L A C =
      M.closure (layerNominal M hE κ k L A ∪ (C ∩ layerBatch M hE κ k L A : Finset α)) := by
  unfold layerUpdate
  congr 1
  ext e
  simp only [layerBatch, Set.mem_union, Set.mem_inter_iff, mem_coe, mem_inter, mem_filter]
  tauto

noncomputable def runReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Set α
  | [], A, _ => A
  | L::Ls, A, C => runReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

noncomputable def reverseExposureTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → RevealTree α (Set α)
  | [], A => .leaf A
  | L::Ls, A =>
      revealBatch (layerBatch M hE κ k L A).toList (fun I =>
        reverseExposureTree M hE κ k Ls (M.closure (layerNominal M hE κ k L A ∪ (I : Set α))))

lemma reverseExposureTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α) :
    (reverseExposureTree M hE κ k Ls A).Fresh V := by
  induction Ls generalizing V A with
  | nil => trivial
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    apply revealBatch_fresh _ (nodup_toList _) _ V
    · simp only [toList_toFinset]
      intro e he
      exact hV L (by simp) (mem_filter.mpr ⟨(mem_filter.mp he).1, (mem_filter.mp he).2.1⟩)
    · intro I hI
      simp only [toList_toFinset]
      apply ih hdisj.2
      intro L' hL' e he
      refine mem_sdiff.mpr ⟨hV L' (by simp [hL']) he, ?_⟩
      intro hb
      have heL := (mem_filter.mp hb).1
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') heL (mem_filter.mp he).1

lemma layerUpdate_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (L : ReverseLayer α) (A : Set α) (C C' : Finset α)
    (hC : ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    layerUpdate M hE κ k L A C = layerUpdate M hE κ k L A C' := by
  unfold layerUpdate
  congr 1
  ext e
  by_cases heG : e ∈ L.group
  · simp only [Set.mem_union, Set.mem_inter_iff, mem_coe, hC e heG]
  · simp [heG]

lemma runReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    runReverseLayers M hE κ k Ls A C = runReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [runReverseLayers, runReverseLayers, layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).run C = runReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_run _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, runReverseLayers]
    apply runReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

theorem reverseExposure_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (V : Finset α) (hV : ∀ L ∈ Ls, (L.group.filter (fun e => e ∈ L.state)) ⊆ V) (A : Set α)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (runReverseLayers M hE κ k Ls A C) *
        ψ ((reverseExposureTree M hE κ k Ls A).hybrid C T))) =
      bitsExpectation q V (fun C => φ (runReverseLayers M hE κ k Ls A C)) *
        bitsExpectation q V ψ := by
  have h := (reverseExposureTree M hE κ k Ls A).hybrid_independent q V
    (reverseExposureTree_fresh M hE κ k Ls hdisj V hV A) φ ψ
  simpa only [reverseExposureTree_run M hE κ k Ls hdisj] using h

omit [DecidableEq α] in
lemma runReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    runReverseLayers M hE κ k (Ls ++ Ls') A C =
      runReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih => exact ih _

def sourceLayer (D S : ℕ → Set α) (G : ℕ → Finset α) (j : ℕ) : ReverseLayer α :=
  ⟨G j, D j, S j, activation j⟩

def sourceLayers (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) : List (ReverseLayer α) :=
  (List.range n).map (sourceLayer D S G)

omit [Fintype α] [DecidableEq α] in
lemma sourceLayers_pairwise (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) :
    (sourceLayers D S G n).Pairwise (fun L L' => Disjoint L.group L'.group) := by
  rw [sourceLayers, List.pairwise_map]
  exact (List.nodup_range (n := n)).pairwise_of_forall_ne (fun _ _ _ _ hij => hG hij)

omit [DecidableEq α] in
lemma runReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    runReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      runReverseLayers_append]
    change layerUpdate M hE κ k (sourceLayer D S G n)
      (runReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C) C = _
    rw [ih]
    rfl

theorem source_reverse_hybrid_independent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (φ : Set α → ℝ) (ψ : Finset α → ℝ) :
    let tree := reverseExposureTree M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ)
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
        ψ (tree.hybrid C T))) =
      bitsExpectation q V (fun C =>
        φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n)) *
          bitsExpectation q V ψ := by
  dsimp only
  have hv : ∀ L ∈ sourceLayers D S G n, L.group.filter (fun e => e ∈ L.state) ⊆ V := by
    intro L hL
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
    exact hV j (List.mem_range.mp hj)
  have h := reverseExposure_hybrid_independent M hE κ k (sourceLayers D S G n)
    (sourceLayers_pairwise D S G n hG) V hv
      (if k < 0 then M.closure ∅ else Set.univ) q φ ψ
  simpa only [runReverseLayers_source] using h

noncomputable def queriedReverseLayers (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) : List (ReverseLayer α) → Set α → Finset α → Finset α
  | [], _, _ => ∅
  | L::Ls, A, C => layerBatch M hE κ k L A ∪
      queriedReverseLayers M hE κ k Ls (layerUpdate M hE κ k L A C) C

lemma queriedReverseLayers_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α)) (A : Set α) (C C' : Finset α)
    (hC : ∀ L ∈ Ls, ∀ e ∈ L.group, (e ∈ C ↔ e ∈ C')) :
    queriedReverseLayers M hE κ k Ls A C = queriedReverseLayers M hE κ k Ls A C' := by
  induction Ls generalizing A with
  | nil => rfl
  | cons L Ls ih =>
    rw [queriedReverseLayers, queriedReverseLayers,
      layerUpdate_congr M hE κ k L A C C' (hC L (by simp))]
    congr 1
    exact ih _ (fun L' hL' => hC L' (by simp [hL']))

lemma reverseExposureTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls : List (ReverseLayer α))
    (hdisj : Ls.Pairwise (fun L L' => Disjoint L.group L'.group))
    (A : Set α) (C : Finset α) :
    (reverseExposureTree M hE κ k Ls A).queried C = queriedReverseLayers M hE κ k Ls A C := by
  induction Ls generalizing A C with
  | nil => rfl
  | cons L Ls ih =>
    rw [List.pairwise_cons] at hdisj
    rw [reverseExposureTree, revealBatch_queried _ (nodup_toList _)]
    simp only [toList_toFinset]
    rw [ih hdisj.2, ← layerUpdate_eq_batch, queriedReverseLayers]
    congr 1
    apply queriedReverseLayers_congr
    intro L' hL' e he
    have heB : e ∉ layerBatch M hE κ k L A := by
      intro hb
      exact Finset.disjoint_left.mp (hdisj.1 L' hL') (mem_filter.mp hb).1 he
    simp [heB]

lemma queriedReverseLayers_append (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (Ls Ls' : List (ReverseLayer α)) (A : Set α) (C : Finset α) :
    queriedReverseLayers M hE κ k (Ls ++ Ls') A C = queriedReverseLayers M hE κ k Ls A C ∪
      queriedReverseLayers M hE κ k Ls' (runReverseLayers M hE κ k Ls A C) C := by
  induction Ls generalizing A with
  | nil => simp [queriedReverseLayers, runReverseLayers]
  | cons L Ls ih =>
    simp only [List.cons_append, queriedReverseLayers, runReverseLayers, ih, union_assoc]

lemma queriedReverseLayers_source (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    queriedReverseLayers M hE κ k (sourceLayers D S G n)
      (if k < 0 then M.closure ∅ else Set.univ) C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  induction n with
  | zero => simp [sourceLayers, queriedReverseLayers]
  | succ n ih =>
    simp only [sourceLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      queriedReverseLayers_append]
    change queriedReverseLayers M hE κ k (sourceLayers D S G n)
        (if k < 0 then M.closure ∅ else Set.univ) C ∪
      (layerBatch M hE κ k (sourceLayer D S G n)
        (runReverseLayers M hE κ k (sourceLayers D S G n)
          (if k < 0 then M.closure ∅ else Set.univ) C) ∪ ∅) = _
    rw [ih, runReverseLayers_source]
    simp only [union_empty, Finset.range_add_one, biUnion_insert]
    rw [union_comm]
    rfl

end MatroidProphet

end OAI
