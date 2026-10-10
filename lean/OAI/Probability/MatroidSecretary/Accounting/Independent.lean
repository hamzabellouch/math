import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Source-exact accounting contracts

The conditioning in `lem:all-orders` fixes every test bit outside the focal
listed group.  Averaging only the remaining group's bits is stronger than
merely averaging all test bits.  We make that finite conditional expectation
explicit below, without conditioning on any arrival order.
-/

namespace MatroidProphet.AccountingIndependent

open Set Finset Pivots

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The manuscript's test-thinning inequality for each fixed outside-mask
realization. `A` is exactly the fixed positive test set outside `G h`; only
`B ⊆ G h` is averaged. In particular, no selected arrival order is conditioned
on, and the competition set may depend on all outside bits. -/
theorem thinning_finalRankStatistic_conditioned
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h final : ℕ) (O : Set α) (ε : Fin 2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A : Finset α) (hA : Disjoint A (G h)) :
    t * (finalRankStatistic M hE κ D C
      (fun j => (A : Set α) ∩ (G j : Set α)) h final (G h) O Set.univ ε : ℝ) ≤
    bitsExpectation (fun _ : α => t) (G h) (fun B =>
      (finalRankStatistic M hE κ D C
        (fun j => ((A ∪ B : Finset α) : Set α) ∩ (G j : Set α))
        h final (G h) O ((A ∪ B : Finset α) : Set α) ε : ℝ)) := by
  classical
  simp only [finalRankStatistic, Set.inter_univ, Nat.cast_sum,
    bitsExpectation_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  let S := nominalLayerSet M hE κ D C h (G h) ε b \ O
  have hS : S ⊆ (G h : Set α) := fun e he =>
    nominalLayerSet_subset M hE κ D C h (G h) ε b he.1
  have hdis : S ∩ (A : Set α) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heS, heA⟩
    exact Finset.disjoint_left.mp hA heA (hS heS)
  have ht := independent_thinning_rank M hE (G h) S.toFinset
    (fun e he => hS (by simpa only [Set.mem_toFinset] using he))
    (guardedPath M hE κ D C final (b.val.val - 2) ∪
      lowerCompetition M hE κ D C
        (fun j => (A : Set α) ∩ (G j : Set α)) b.val.val h) t ht0 ht1
  calc
    _ ≤ bitsExpectation (fun _ : α => t) (G h) (fun B =>
        (conditionalRank M (S ∩ (B : Set α))
          (guardedPath M hE κ D C final (b.val.val - 2) ∪
            lowerCompetition M hE κ D C
              (fun j => (A : Set α) ∩ (G j : Set α)) b.val.val h) : ℝ)) := by
      simpa only [Finset.coe_inter, Set.coe_toFinset] using ht
    _ = _ := by
      apply bitsExpectation_congr
      intro B hB
      rw [lowerCompetition_ignore_focal M hE κ D C G hG b.val.val h A B hB]
      have heq : S ∩ ((A ∪ B : Finset α) : Set α) = S ∩ (B : Set α) := by
        rw [Finset.coe_union, Set.inter_union_distrib_left, hdis, Set.empty_union]
      change (conditionalRank M (S ∩ (B : Set α)) _ : ℝ) =
        (conditionalRank M (S ∩ ((A ∪ B : Finset α) : Set α)) _ : ℝ)
      rw [heq]

/-- The unscaled real-valued form of `lem:rank-cost`. There is a single
sum of later-group costs for the entire parity timeline, not one cost per
layer. The density contribution is real division, never truncated division. -/
theorem rank_cost_real
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (U O : Set α) (ε : Fin 2) :
    (nominalRankStatistic M hE κ D C T h U O ε : ℝ) -
      ((C h).ncard + ∑ j ∈ Finset.range later,
        ((C (h+1+j)).ncard + (D (h+1+j)).ncard / (κ : ℝ))) ≤
    (finalRankStatistic M hE κ D C T h (h+1+later) U O Set.univ ε : ℝ) := by
  have hn := testRankStatistic_le_final_cost M hE κ hκ D C T h later U O Set.univ ε
  have heq : testRankStatistic M hE κ D C T h U O Set.univ ε =
      nominalRankStatistic M hE κ D C T h U O ε := by
    simp only [testRankStatistic, nominalRankStatistic, Set.inter_univ]
  rw [heq] at hn
  have hr : (κ : ℝ) * (nominalRankStatistic M hE κ D C T h U O ε : ℝ) ≤
      (κ : ℝ) * (finalRankStatistic M hE κ D C T h (h+1+later) U O Set.univ ε : ℝ) +
        (κ : ℝ) * (C h).ncard +
        ∑ j ∈ Finset.range later,
          ((κ : ℝ) * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
    exact_mod_cast hn
  have hkpos : (0 : ℝ) < κ := Nat.cast_pos.mpr hκ
  have hcost : (κ : ℝ) *
      ((C h).ncard + ∑ j ∈ Finset.range later,
        ((C (h+1+j)).ncard + (D (h+1+j)).ncard / (κ : ℝ))) =
      (κ : ℝ) * (C h).ncard + ∑ j ∈ Finset.range later,
        ((κ : ℝ) * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hkpos)]
  nlinarith

open MainAlgorithm

/-- Both assertions of source `lem:all-orders`, instantiated to the actual
listed groups. The second assertion is the finite conditional law obtained by
fixing all of `H,D,C`, parity, and every test bit outside the listed group. -/
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
  constructor
  · intro π
    exact listedLambda_le_count M hE d w π h
  · intro A hA
    have ht := thinning_finalRankStatistic_conditioned M hE (2^100)
      (groupMask M d w d.D) (groupMask M d w d.C) (pathGroups M d w)
      (pathGroups_disjoint M d w) h (groups M d w).length
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)
      thinningRate constants_positive.2.2.1.le (by norm_num [thinningRate]) A hA
    simpa only [listedLambda_update_T] using ht

/-- Source `lem:rank-cost` for the concrete listed group and final guarded
path, with the displayed real-valued cost and without any probabilistic or
independence assumption on its common generators. -/
theorem listed_rank_cost {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ)
    (hh : h < (groups M d w).length) :
    (listedZ M hE d w h : ℝ) -
      ((groupMask M d w d.C h).ncard +
        ∑ j ∈ Finset.range ((groups M d w).length - (h+1)),
          ((groupMask M d w d.C (h+1+j)).ncard +
            (groupMask M d w d.D (h+1+j)).ncard / densityThreshold)) ≤
    (finalRankStatistic M hE (2^100)
      (groupMask M d w d.D) (groupMask M d w d.C) (groupMask M d w d.T)
      h (groups M d w).length (groupMask M d w Finset.univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
      (boolParity d.odd) : ℝ) := by
  have hc := rank_cost_real M hE (2^100) (by positivity)
    (groupMask M d w d.D) (groupMask M d w d.C) (groupMask M d w d.T)
    h ((groups M d w).length - (h+1)) (groupMask M d w Finset.univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)
  have hlen : h+1+((groups M d w).length - (h+1)) = (groups M d w).length := by omega
  rw [hlen] at hc
  simpa only [listedZ, densityThreshold, Nat.cast_pow, Nat.cast_ofNat] using hc

end MatroidProphet.AccountingIndependent

end OAI
