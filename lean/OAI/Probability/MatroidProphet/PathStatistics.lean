import OAI.Probability.MatroidProphet.RankCost
import OAI.Probability.MatroidProphet.Residual.Statistics
import OAI.Probability.MatroidProphet.ConditionalThinning

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma lowerCompetition_congr_test_before (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T T' : ℕ → Set α) (b : ℤ) (h : ℕ)
    (hT : ∀ j < h, T j = T' j) :
    lowerCompetition M hE κ D C T b h = lowerCompetition M hE κ D C T' b h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [lowerCompetition]
    rw [ih (fun j hj => hT j (by omega)), hT h (by omega)]

lemma lowerCompetition_ignore_focal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (b : ℤ) (h : ℕ)
    (A B : Finset α) (hB : B ⊆ G h) :
    lowerCompetition M hE κ D C (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α)) b h =
      lowerCompetition M hE κ D C (fun j => (A : Set α) ∩ (G j : Set α)) b h := by
  apply lowerCompetition_congr_test_before
  intro j hj
  ext e
  have hd := Finset.disjoint_left.mp (hG (show h ≠ j by omega))
  simp only [Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
  constructor
  · rintro ⟨ha | hb, hg⟩
    · exact ⟨ha, hg⟩
    · exact False.elim (hd (hB hb) hg)
  · rintro ⟨ha, hg⟩
    exact ⟨Or.inl ha, hg⟩

noncomputable def testRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

noncomputable def finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h final : ℕ) (U O test : Set α) (ε : Fin 2) : ℕ :=
  ∑ b : ParityWindow (activation h) ε,
    conditionalRank M ((nominalLayerSet M hE κ D C h U ε b \ O) ∩ test)
      (guardedPath M hE κ D C final (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)

theorem thinning_nominalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε : ℝ)) ≤
    bitsExpectation (fun _ : α => t) univ (fun T =>
      (testRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O (T : Set α) ε : ℝ)) := by
  simp only [nominalRankStatistic, testRankStatistic, Nat.cast_sum, bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply conditionally_independent_thinning_rank M hE t ht0 ht1 univ (G h) (subset_univ _)
  · exact fun e he => (nominalLayerSet_subset M hE κ D C h (G h) ε b he.1)
  · intro A B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

omit [DecidableEq α] in
lemma unobservedBirthRegion_eq_nominalLayer (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U O : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) :
    unobservedBirthRegion M hE κ D C U O h b.val.val =
      nominalLayerSet M hE κ D C h U ε b \ O := by
  classical
  ext e
  unfold unobservedBirthRegion nominalLayerSet
  by_cases ha : activation h+2 ≤ b.val.val
  · rw [ite_eq_left ha]
    constructor
    · rintro ⟨⟨hu, hx, hn⟩, ho⟩
      have hb : b.val.val ≤ 0 := by
        by_contra hb
        have heq := nominalPath_nonnegative M hE κ D C h (show 0 ≤ b.val.val-1 by omega)
        rw [heq] at hn
        exact hn (Set.mem_univ e)
      exact ⟨⟨hu, ha, hb, hx, hn⟩, ho⟩
    · rintro ⟨⟨hu, _, _, hx, hn⟩, ho⟩
      exact ⟨⟨hu, hx, hn⟩, ho⟩
  · rw [ite_eq_right ha]
    simp only [Set.mem_empty_iff_false, Set.mem_sdiff, Set.mem_ofPred_eq, false_iff,
      not_and]
    intro he
    exact (ha he.2.1).elim

theorem testRankStatistic_le_final_cost
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (U O test : Set α) (ε : Fin 2) :
    κ * testRankStatistic M hE κ D C T h U O test ε ≤
      κ * finalRankStatistic M hE κ D C T h (h+1+later) U O test ε +
        κ * (C h).ncard +
          ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  let S : ℤ → Set α := fun b => unobservedBirthRegion M hE κ D C U O h b ∩ test
  have hc := actual_path_rank_cost_finset M hE κ hκ D C T h later
    (parityPoints (activation h) ε) (activation h-4) 1
    (by dsimp [activation]; omega)
    (by intro b hb; have := (mem_parityPoints _ _ _).mp hb; omega)
    (by intro b hb; exact ((mem_parityPoints _ _ _).mp hb).2.1)
    (by
      intro b hb c hc hbc
      have hbm := ((mem_parityPoints _ _ _).mp hb).2.2
      have hcm := ((mem_parityPoints _ _ _).mp hc).2.2
      omega)
    S (fun b e he => unobservedBirthRegion_subset M hE κ D C U O h b he.1)
  rw [sum_parityPoints, sum_parityPoints] at hc
  have hS (b : ParityWindow (activation h) ε) : S b.val.val =
      (nominalLayerSet M hE κ D C h U ε b \ O) ∩ test := by
    dsimp [S]
    rw [unobservedBirthRegion_eq_nominalLayer M hE κ D C h U O ε b]
  simp_rw [hS] at hc
  exact hc

theorem thinning_finalRankStatistic (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O Set.univ ε : ℝ)) ≤
    bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h final
        (G h) O (T : Set α) ε : ℝ)) := by
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum, bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply conditionally_independent_thinning_rank M hE t ht0 ht1 univ (G h) (subset_univ _)
  · exact fun e he => (nominalLayerSet_subset M hE κ D C h (G h) ε b he.1)
  · intro A B hB
    rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]

theorem expected_nominal_to_final (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h later : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (κ:ℝ) * t * bitsExpectation (fun _ : α => t) univ (fun T =>
      (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε : ℝ)) ≤
    (κ:ℝ) * bitsExpectation (fun _ : α => t) univ (fun T =>
      (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α)) h
        (h+1+later) (G h) O (T : Set α) ε : ℝ)) +
      t * (κ * (C h).ncard + ∑ j ∈ range later,
        (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
  have ht := thinning_finalRankStatistic M hE κ D C G hG h (h+1+later) O ε t ht0 ht1
  have hp (T : Finset α) :
      (κ:ℝ) * (nominalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O ε : ℝ) ≤
      (κ:ℝ) * (finalRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (h+1+later) (G h) O Set.univ ε : ℝ) +
        (κ * (C h).ncard + ∑ j ∈ range later,
          (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) : ℕ) := by
    have hn := testRankStatistic_le_final_cost M hE κ hκ D C
      (fun j => (T : Set α) ∩ (G j : Set α)) h later (G h) O Set.univ ε
    have htest : testRankStatistic M hE κ D C (fun j => (T : Set α) ∩ (G j : Set α))
        h (G h) O Set.univ ε = nominalRankStatistic M hE κ D C
        (fun j => (T : Set α) ∩ (G j : Set α)) h (G h) O ε := by
      simp only [testRankStatistic, nominalRankStatistic, Set.inter_univ]
    rw [htest, Nat.add_assoc] at hn
    exact_mod_cast hn
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    univ (fun T _ => hp T)
  simp only [bitsExpectation_add, bitsExpectation_mul_left, bitsExpectation_const] at hm
  have hs := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg κ : (0:ℝ) ≤ κ)
  have hc := mul_le_mul_of_nonneg_left hm ht0
  nlinarith

end MatroidProphet

end OAI
