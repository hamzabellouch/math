import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The manuscript writes the observed rank mask as `D ∪ C`, whereas the
algorithm also removes `H`.  The two definitions coincide on every candidate
group, including empty and unlisted groups.  These lemmas discharge that
semantic identification without adding a premise to a source theorem. -/

namespace MatroidProphet.SourceRankMask
open Set Finset MainAlgorithm
variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma sdiff_union_of_subset_disjoint (S U H O : Set α)
    (hSU : S ⊆ U) (hUH : Disjoint U H) : S \ (H ∪ O) = S \ O := by
  ext e
  constructor
  · rintro ⟨he, hn⟩
    exact ⟨he, fun ho => hn (Or.inr ho)⟩
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    rintro (hh | ho)
    · exact Set.disjoint_left.mp hUH (hSU he) hh
    · exact hn ho

lemma nominalLayerSet_sdiff_union (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U H O : Set α) (ε : Fin 2)
    (b : Pivots.ParityWindow (activation h) ε) (hUH : Disjoint U H) :
    nominalLayerSet M hE κ D C h U ε b \ (H ∪ O) =
      nominalLayerSet M hE κ D C h U ε b \ O :=
  sdiff_union_of_subset_disjoint _ U H O
    (nominalLayerSet_subset M hE κ D C h U ε b) hUH

lemma nominalRankStatistic_mask_union (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U H O : Set α) (ε : Fin 2)
    (hUH : Disjoint U H) :
    nominalRankStatistic M hE κ D C T h U (H ∪ O) ε =
      nominalRankStatistic M hE κ D C T h U O ε := by
  unfold nominalRankStatistic
  apply Finset.sum_congr rfl
  intro b _
  rw [nominalLayerSet_sdiff_union M hE κ D C h U H O ε b hUH]

lemma testRankStatistic_mask_union (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U H O test : Set α) (ε : Fin 2)
    (hUH : Disjoint U H) :
    testRankStatistic M hE κ D C T h U (H ∪ O) test ε =
      testRankStatistic M hE κ D C T h U O test ε := by
  unfold testRankStatistic
  apply Finset.sum_congr rfl
  intro b _
  rw [nominalLayerSet_sdiff_union M hE κ D C h U H O ε b hUH]

lemma finalRankStatistic_mask_union (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h final : ℕ) (U H O test : Set α) (ε : Fin 2)
    (hUH : Disjoint U H) :
    finalRankStatistic M hE κ D C T h final U (H ∪ O) test ε =
      finalRankStatistic M hE κ D C T h final U O test ε := by
  unfold finalRankStatistic
  apply Finset.sum_congr rfl
  intro b _
  rw [nominalLayerSet_sdiff_union M hE κ D C h U H O ε b hUH]

variable {n : ℕ}

lemma groupMask_disjoint_H (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) :
    Disjoint (groupMask M d w mask h) (d.H : Set (Fin n)) := by
  apply Set.disjoint_left.mpr
  intro e he hh
  exact he.2.1.2.1 hh

/-- Exact source mask for the nominal statistic; no listing hypothesis. -/
lemma listedZ_sourceMask (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) :
    listedZ M hE d w h =
      nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (groupMask M d w d.T) h (groupMask M d w univ h)
        ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) := by
  unfold listedZ
  simpa only [Finset.coe_union, Set.union_assoc] using
    nominalRankStatistic_mask_union M hE (2^100) (groupMask M d w d.D)
      (groupMask M d w d.C) (groupMask M d w d.T) h (groupMask M d w univ h)
      (d.H : Set (Fin n)) ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n))
      (boolParity d.odd) (groupMask_disjoint_H M d w univ h)

/-- Exact source mask for the final statistic used in the all-orders bound. -/
lemma listedLambda_sourceMask (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) :
    listedLambda M hE d w h =
      finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (groupMask M d w d.T) h (groups M d w).length (groupMask M d w univ h)
        ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (d.T : Set (Fin n))
        (boolParity d.odd) := by
  unfold listedLambda
  simpa only [Finset.coe_union, Set.union_assoc] using
    finalRankStatistic_mask_union M hE (2^100) (groupMask M d w d.D)
      (groupMask M d w d.C) (groupMask M d w d.T) h (groups M d w).length
      (groupMask M d w univ h) (d.H : Set (Fin n))
      ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (d.T : Set (Fin n))
      (boolParity d.odd) (groupMask_disjoint_H M d w univ h)

/-- Exact nominal statistic in the transfer section, including its zero branch. -/
lemma listedRankStatistic_sourceMask (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) :
    listedRankStatistic M hE κ d w i ε =
      if i ∈ groups M d w then
        nominalRankStatistic M hE κ (groupMask M d w d.D) (groupMask M d w d.C)
          (groupMask M d w d.T) ((groups M d w).idxOf i)
          (trueGroup M d w i : Set (Fin n))
          ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) ε
      else 0 := by
  classical
  have hUH : Disjoint (trueGroup M d w i : Set (Fin n)) (d.H : Set (Fin n)) := by
    apply Set.disjoint_left.mpr
    intro e he hh
    exact ((mem_trueGroup M d w i e).mp he).1.2.1 hh
  unfold listedRankStatistic
  split_ifs
  · simpa only [Finset.coe_union, Set.union_assoc] using
      nominalRankStatistic_mask_union M hE κ (groupMask M d w d.D)
        (groupMask M d w d.C) (groupMask M d w d.T) ((groups M d w).idxOf i)
        (trueGroup M d w i : Set (Fin n)) (d.H : Set (Fin n))
        ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) ε hUH
  · rfl

end MatroidProphet.SourceRankMask

end OAI
