import OAI.Probability.MatroidProphet.Reverse.Exposure

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def sourceReverseTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (Set α) :=
  reverseExposureTree M hE κ k (sourceLayers D S G n)
    (if k < 0 then M.closure ∅ else Set.univ)

lemma sourceReverseTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (sourceReverseTree M hE κ k D S G n).Fresh V := by
  apply reverseExposureTree_fresh M hE κ k _ (sourceLayers_pairwise D S G n hG)
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hL
  exact hV j (List.mem_range.mp hj)

lemma sourceReverseTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) :
    (sourceReverseTree M hE κ k D S G n).queried C =
      (Finset.range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j ∧
        e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j)) := by
  rw [sourceReverseTree, reverseExposureTree_queried M hE κ k _
    (sourceLayers_pairwise D S G n hG), queriedReverseLayers_source]

lemma sourceReverseTree_queried_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2.2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, heS, he⟩⟩

lemma sourceReverseTree_hybrid_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) (heS : e ∈ S j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).hybrid C T ↔
      (e ∈ C ∧ e ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∨
      (e ∈ T ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) := by
  rw [(sourceReverseTree M hE κ k D S G n).hybrid_eq_resample V C T
    (sourceReverseTree_fresh M hE κ k D S G n hG V hV) hC hT]
  simp only [mem_union, mem_sdiff, mem_inter,
    sourceReverseTree_queried_coordinate M hE κ k D S G n hG C hj heG heS, not_not]

noncomputable def transitionHybrid (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (j : ℕ) : Set α :=
  ((C : Set α) ∩ (G j : Set α) ∩
    reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j) ∪
  ((T : Set α) ∩ (G j : Set α) ∩
    (S j \ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j))

lemma sourceReverseTree_hybrid_guard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) {j : ℕ} (hj : j < n) :
    (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α)) ∩ S j =
      transitionHybrid M hE κ k D S G C T j ∩ S j := by
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · have hh := sourceReverseTree_hybrid_coordinate M hE κ k D S G n hG V hV C T hC hT hj heG heS
      simp only [transitionHybrid, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, and_true, true_and]
      exact hh
    · simp [transitionHybrid, heS]
  · simp [transitionHybrid, heG]

omit [DecidableEq α] in
lemma reversePrefix_congr_guard_inter (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C C' S : ℕ → Set α) (k : ℤ) (n : ℕ)
    (hC : ∀ j < n, C j ∩ S j = C' j ∩ S j) :
    reversePrefix M hE κ D C S k n = reversePrefix M hE κ D C' S k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega)), hC n (by omega)]

lemma sourceReverseTree_hybrid_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (C T : Finset α) (hC : C ⊆ V) (hT : T ⊆ V) :
    reverseNominal M hE κ D
      (fun j => (((sourceReverseTree M hE κ k D S G n).hybrid C T : Set α) ∩ (G j : Set α))) S k n =
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n := by
  unfold reverseNominal
  congr 1
  exact reversePrefix_congr_guard_inter M hE κ D _ _ S k n
    (fun j hj => sourceReverseTree_hybrid_guard M hE κ k D S G n hG V hV C T hC hT hj)

theorem reverse_double_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (q : α → ℝ) (d : α) :
    bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      (if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0) *
      (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V (fun C =>
        if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0)) ^ 2 := by
  let φ : Set α → ℝ := fun A => if d ∉ densityEnabled M hE κ (D n) (activation n) k A then 1 else 0
  let ψ : Finset α → ℝ := fun C =>
    if d ∉ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n then 1 else 0
  have hi := source_reverse_hybrid_independent M hE κ k D S G n hG V hV q φ ψ
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      (bitsExpectation q V ψ)^2
  have heq : bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
      ψ C * (if d ∉ reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n then 1 else 0))) =
      bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
        ψ C * ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    dsimp only [ψ]
    rw [sourceReverseTree_hybrid_output M hE κ k D S G n hG V hV C T hC hT]
  rw [heq]
  change bitsExpectation q V (fun C => bitsExpectation q V (fun T =>
    φ (reversePrefix M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n) *
      ψ ((sourceReverseTree M hE κ k D S G n).hybrid C T))) = _
  unfold sourceReverseTree
  rw [hi]
  change bitsExpectation q V ψ * bitsExpectation q V ψ = _
  ring

lemma sourceReverseTree_queried_coordinate_full (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) {e : α} (heG : e ∈ G j) :
    e ∈ (sourceReverseTree M hE κ k D S G n).queried C ↔
      e ∈ S j ∧ e ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [sourceReverseTree_queried M hE κ k D S G n hG, mem_biUnion]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hij : i = j
    · subst i; exact (mem_filter.mp he).2
    · exact (Finset.disjoint_left.mp (hG hij) (mem_filter.mp he).1 heG).elim
  · intro he
    exact ⟨j, mem_range.mpr hj, mem_filter.mpr ⟨heG, he⟩⟩

lemma sourceReverseTree_positive_guards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j < n) :
    ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G j : Set α) =
      departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  ext e
  by_cases heG : e ∈ G j
  · have hq := sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG
    simp only [departingGuards, Set.mem_inter_iff, Set.mem_sdiff, mem_coe, mem_inter, heG, and_true]
    rw [hq]
  · simp [departingGuards, heG]

lemma sourceReverseTree_positive_nominal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α)
    {j : ℕ} (hj : j ≤ n) :
    reverseNominal M hE κ D
      (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α))
      S k j = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  calc
    _ = reverseNominal M hE κ D
        (departingGuards M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k) S k j := by
      apply reverseNominal_congr_before
      · intro i hi
        exact sourceReverseTree_positive_guards M hE κ k D S G n hG C (by omega)
      · exact fun _ _ => rfl
    _ = _ := reverseNominal_departing_only M hE κ D _ S k j

noncomputable def reverseStateTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (Fin n → Set α) :=
  (sourceReverseTree M hE κ k D S G n).record.map (fun r j =>
    reverseNominal M hE κ D (fun i => (r.positive : Set α) ∩ (G i : Set α)) S k j.val)

lemma reverseStateTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) :
    (reverseStateTree M hE κ k D S G n).run C =
      (fun j => reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j.val) := by
  rw [reverseStateTree, RevealTree.run_map, RevealTree.record_run]
  funext j
  exact sourceReverseTree_positive_nominal M hE κ k D S G n hG C j.isLt.le

lemma reverseStateTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (reverseStateTree M hE κ k D S G n).Fresh V := by
  rw [reverseStateTree, RevealTree.fresh_map, RevealTree.record_fresh]
  exact sourceReverseTree_fresh M hE κ k D S G n hG V hV

lemma reverseStateTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStateTree M hE κ k D S G n).queried C =
      (sourceReverseTree M hE κ k D S G n).queried C := by
  rw [reverseStateTree, RevealTree.queried_map, RevealTree.record_queried]

end MatroidProphet

end OAI
