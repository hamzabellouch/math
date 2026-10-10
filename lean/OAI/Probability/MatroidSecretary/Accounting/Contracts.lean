import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Source-facing accounting lemmas. In particular, the thinning assertion is
proved on each fixed outside-test fiber, not only after averaging those bits. -/

namespace MatroidProphet.AccountingContracts
open Set Finset Pivots

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Fixing all test memberships outside the focal group leaves its Bernoulli
rank lower bound intact. This is the finite conditional law in `lem:all-orders`. -/
theorem thinning_final_fixed_outside
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A : Finset α) (hA : Disjoint A (G h)) :
    t * (finalRankStatistic M hE κ D C
      (fun j => (A : Set α) ∩ (G j : Set α)) h final
      (G h) O Set.univ ε : ℝ) ≤
    bitsExpectation (fun _ : α => t) (G h) (fun B =>
      (finalRankStatistic M hE κ D C
        (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α)) h final
        (G h) O ((A ∪ B : Finset α) : Set α) ε : ℝ)) := by
  classical
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum,
    bitsExpectation_sum, mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  let S := nominalLayerSet M hE κ D C h (G h) ε b \ O
  have hS : S ⊆ (G h : Set α) :=
    fun e he => nominalLayerSet_subset M hE κ D C h (G h) ε b he.1
  have hin := independent_thinning_rank M hE (G h) S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he))
    (guardedPath M hE κ D C final (b.val.val - 2) ∪
      lowerCompetition M hE κ D C
        (fun j => (A : Set α) ∩ (G j : Set α)) b.val.val h) t ht0 ht1
  simp only [Set.coe_toFinset, Finset.coe_inter] at hin
  apply hin.trans_eq
  apply bitsExpectation_congr
  intro B hB
  rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]
  have hs : S ∩ ((A ∪ B : Finset α) : Set α) = S ∩ (B : Set α) := by
    ext e
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_union]
    constructor
    · rintro ⟨he, ha | hb⟩
      · exact False.elim (Finset.disjoint_left.mp hA ha (hS he))
      · exact ⟨he, hb⟩
    · rintro ⟨he, hb⟩
      exact ⟨he, Or.inr hb⟩
  change (conditionalRank M (S ∩ (B : Set α)) _ : ℝ) =
    (conditionalRank M (S ∩ ((A ∪ B : Finset α) : Set α)) _ : ℝ)
  rw [hs]

/-- The manuscript's real-valued one-budget rank loss, before test thinning.
The bound is valid for the entire finite parity window, including empty layers. -/
theorem nominal_rank_le_final_add_cost
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (U O : Set α) (ε : Fin 2) :
    (nominalRankStatistic M hE κ D C T h U O ε : ℝ) ≤
      (finalRankStatistic M hE κ D C T h (h+1+later) U O Set.univ ε : ℝ) +
      (C h).ncard + ∑ j ∈ range later,
        ((C (h+1+j)).ncard + (D (h+1+j)).ncard / (κ : ℝ)) := by
  have hn := testRankStatistic_le_final_cost M hE κ hκ D C T h later U O Set.univ ε
  have heq : testRankStatistic M hE κ D C T h U O Set.univ ε =
      nominalRankStatistic M hE κ D C T h U O ε := by
    simp only [testRankStatistic, nominalRankStatistic, Set.inter_univ]
  rw [heq] at hn
  have hr : (κ : ℝ) * (nominalRankStatistic M hE κ D C T h U O ε : ℝ) ≤
      (κ : ℝ) * (finalRankStatistic M hE κ D C T h (h+1+later) U O Set.univ ε : ℝ) +
      (κ : ℝ) * (C h).ncard + ∑ j ∈ range later,
        ((κ : ℝ) * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
    exact_mod_cast hn
  have hk : (0 : ℝ) < κ := by exact_mod_cast hκ
  apply (mul_le_mul_iff_right₀ hk).mp
  have hs : (κ : ℝ) * (∑ j ∈ range later,
      ((C (h+1+j)).ncard + (D (h+1+j)).ncard / (κ : ℝ))) =
      ∑ j ∈ range later, ((κ : ℝ) * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [mul_add]
    congr 1
    field_simp
  rw [mul_add, mul_add, hs]
  exact hr

open MainAlgorithm in
/-- Both source clauses of the order-uniform rank bound: deterministic domination
for every order, and test thinning on every fixed outside-group fiber. -/
theorem all_orders {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) :
    (∀ π : ArrivalOrder n, listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card) ∧
    (∀ A : Finset (Fin n), Disjoint A (pathGroups M d w h) →
      thinningRate * (finalRankStatistic M hE (2^100)
        (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (A : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)))
        h (groups M d w).length (pathGroups M d w h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
        (boolParity d.odd) : ℝ) ≤
      bitsExpectation (fun _ : Fin n => thinningRate) (pathGroups M d w h)
        (fun B => (listedLambda M hE {d with T := A ∪ B} w h : ℝ))) := by
  classical
  refine ⟨fun π => listedLambda_le_count M hE d w π h, ?_⟩
  intro A hA
  simp only [listedLambda_update_T]
  exact thinning_final_fixed_outside M hE (2^100)
    (groupMask M d w d.D) (groupMask M d w d.C) (pathGroups M d w)
    (pathGroups_disjoint M d w) h (groups M d w).length
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)
    thinningRate (by norm_num [thinningRate]) (by norm_num [thinningRate]) A hA

open MainAlgorithm in
/-- The source telescoping rank-cost assertion for an actual listed group.
All later expansions use one cost over the whole auxiliary path. -/
theorem rank_cost {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ)
    (hh : h < (groups M d w).length) :
    (listedZ M hE d w h : ℝ) ≤
      (finalRankStatistic M hE (2^100) (groupMask M d w d.D)
        (groupMask M d w d.C) (groupMask M d w d.T) h (groups M d w).length
        (groupMask M d w univ h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
        (boolParity d.odd) : ℝ) + (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length-(h+1)),
        ((groupMask M d w d.C (h+1+j)).ncard +
          (groupMask M d w d.D (h+1+j)).ncard / densityThreshold) := by
  have hc := nominal_rank_le_final_add_cost M hE (2^100) (by positivity)
    (groupMask M d w d.D) (groupMask M d w d.C) (groupMask M d w d.T)
    h ((groups M d w).length-(h+1)) (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)
  have hlen : h+1+((groups M d w).length-(h+1)) = (groups M d w).length := by omega
  rw [hlen] at hc
  simpa only [listedZ, densityThreshold, Nat.cast_pow, Nat.cast_ofNat] using hc

end MatroidProphet.AccountingContracts

end OAI
