import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.RestrictWeightSortedEquiv

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets

open Submodule

theorem greedyPivots_weight_le_of_low_span {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ) (hwt : Monotone wt)
    (T B : ℕ) (hspan : span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤) :
    ∀ i ∈ greedyPivots K v T, wt i ≤ B := by
  intro i hi
  by_contra h
  have hiweight : B < wt i := Nat.lt_of_not_ge h
  have hprevious : span K (v '' (Finset.range i : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply span_mono
    apply Set.image_mono
    intro j hj
    apply Finset.mem_range.mpr
    exact lt_of_not_ge (fun hij => (not_le_of_gt (hj.2.trans_lt hiweight)) (hwt hij))
  have hnot := ((mem_greedyPivots_iff v i T).mp hi).2
  apply hnot
  rw [hprevious]
  exact mem_top

theorem span_low_sequence_eq_top_of_coverage {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ)
    (R : α → V) (w : α → ℕ) (T B : ℕ)
    (hcover : ∀ a, w a ≤ B → ∃ j < T, wt j = w a ∧ v j = R a)
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply span_mono
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨j, hj, hjw, hjv⟩ := hcover a ha
  exact ⟨j, ⟨hj, hjw.trans_le ha⟩, hjv⟩

end WeightedTorusJets

namespace WeightedTorusJets

open Submodule

theorem finite_sorted_greedy_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∀ i ∈ greedyPivots K (R ∘ a) s.card, w (a i) ≤ B := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  change ∀ i ∈ greedyPivots K v s.card, w (a i) ≤ B
  by_cases hB₀B : B₀ ≤ B
  · intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    change w (extendFiniteFamily (fun i => (e i : α)) fallback i) ≤ B
    simp only [extendFiniteFamily, dite_eq_left hiT]
    exact ((hs _).mp (e ⟨i, hiT⟩).property).trans hB₀B
  · have hBB₀ : B ≤ B₀ := Nat.le_of_lt (Nat.lt_of_not_ge hB₀B)
    let wt := extendFiniteFamily (fun i => w (e i)) B₀
    have hwt : Monotone wt :=
      monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
    have hcover : ∀ b, w b ≤ B → ∃ j < s.card, wt j = w b ∧ v j = R b := by
      intro b hb
      let j : Fin s.card := e.symm ⟨b, (hs b).mpr (hb.trans hBB₀)⟩
      refine ⟨j, j.isLt, ?_, ?_⟩
      · simp [wt, extendFiniteFamily, j.isLt, j]
      · simp [v, a, extendFiniteFamily, j.isLt, j]
    have hlow := span_low_sequence_eq_top_of_coverage v wt R w s.card B hcover hspan
    intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    have hbound := greedyPivots_weight_le_of_low_span v wt hwt s.card B hlow i hi
    simpa [wt, a, extendFiniteFamily, hiT] using hbound

theorem finiteGreedyPivots_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    ∀ b ∈ finiteGreedyPivots K s R e fallback, w b ≤ B := by
  classical
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact finite_sorted_greedy_weight_le_of_spanning_cutoff
    s R e fallback w B₀ B hs hsort hspan i hi

end WeightedTorusJets

namespace WeightedTorusJets

theorem fixed_first_greedy_rectangle_weight_bound {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (e : Fin (weightedJetIndices H (N ^ 4 - 1)).card ≃ weightedJetIndices H (N ^ 4 - 1))
    (hsort : Monotone (fun i => (e i).1 0 + H * (e i).1 1 + H * (e i).1 2))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    ∀ a ∈ finiteGreedyPivots K (weightedJetIndices H (N ^ 4 - 1)) R e 0,
      (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let B := ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
  have hsets : (weightedJetIndices H B : Set (Fin 3 → ℕ)) = {a | w a ≤ B} := by
    ext a
    exact mem_weightedJetIndices_iff hH a
  have hlow : Submodule.span K (R '' {a : Fin 3 → ℕ | w a ≤ B}) = ⊤ := by
    rw [← hsets]
    exact span_cutoff_eq_top_of_rectangle hH R hspan
  have hbound := finiteGreedyPivots_weight_le_of_spanning_cutoff
    (weightedJetIndices H (N ^ 4 - 1)) R e 0 w (N ^ 4 - 1) B
    (mem_weightedJetIndices_iff hH) hsort hlow
  intro a ha
  exact weightedJetIndices_real_weight hH (by positivity)
    ((mem_weightedJetIndices_iff hH a).mpr (hbound a ha))



theorem finiteGreedyPivots_restrictWeightSortedEquiv_map
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).map e.toEmbedding := by
  classical
  unfold finiteGreedyPivots
  dsimp only
  rw [greedyPivots_restrictWeightSortedEquiv s R w B hs e he fallback,
    Finset.map_eq_image]
  apply Finset.image_congr
  intro i hi
  exact extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i
    (Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi))

theorem finiteGreedyPivots_restrictWeightSortedEquiv
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq α]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).image e := by
  rw [finiteGreedyPivots_restrictWeightSortedEquiv_map, Finset.map_eq_image]
  rfl



theorem sum_embedding_eq_sum_finset_of_range {ι α A : Type*} [Fintype ι]
    [AddCommMonoid A] (p : ι ↪ α) (s : Finset α)
    (hp : Set.range p = (s : Set α)) (f : α → A) :
    ∑ i, f (p i) = ∑ a ∈ s, f a := by
  classical
  have hs : Finset.univ.map p = s := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hp
  rw [← hs, Finset.sum_map]

end WeightedTorusJets


end SiegelZeros

end OAI
