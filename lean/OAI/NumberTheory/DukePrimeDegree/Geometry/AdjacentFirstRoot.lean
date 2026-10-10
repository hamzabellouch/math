import OAI.NumberTheory.DukePrimeDegree.Entropy.FirstRootConditionalProduct

namespace OAI

/-!
# A concrete first adjacent-root product step

The first adjacent root admits a neutral contracting diagonal direction.
Starting the Gaussian chain with this root gives actual local charts to
which the proved conditional-product theorem applies.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_complete_elimination_chain_from_initial {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    (hP : InitialRootPattern P) (hD : PivotsFromPattern P D) :
    ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n := by
  suffices ∀ m : ℕ, ∀ (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)),
      (allPositiveRoots n \ P).card = m → InitialRootPattern P → PivotsFromPattern P D →
      ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n by
    exact this _ P D rfl hP hD
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro P D hcard hP hD
      by_cases hempty : allPositiveRoots n \ P = ∅
      · refine ⟨.done, ?_⟩
        change P = allPositiveRoots n
        apply Finset.Subset.antisymm
        · exact fun p hp => (hP p hp).1
        · exact Finset.sdiff_eq_empty_iff_subset.mp hempty
      · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (allPositiveRoots n \ P)
          (fun q => toLex q) (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hab : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
        have hnot : p ∉ P := (Finset.mem_sdiff.mp hp).2
        have hless : (allPositiveRoots n \ insert p P).card < m := by
          rw [Finset.sdiff_insert, ← hcard]
          exact Finset.card_erase_lt_of_mem hp
        obtain ⟨c, hc⟩ := ih _ hless (insert p P) (insert p.1 D) rfl
          (initialRootPattern_insert_min hP p hp hmin) (pivotsFromPattern_insert hD p.1 p.2)
        exact ⟨.step p.1 p.2 (ne_of_lt hab)
          (initialRootPattern_stable hP hab hnot)
          (initialRootPattern_pivot_notMem hP hD hab hnot) c, hc⟩


lemma adjacent_first_initial (d : ℕ) :
    InitialRootPattern ({((0 : Fin (d + 2)), (1 : Fin (d + 2)))} :
      Finset (Fin (d + 2) × Fin (d + 2))) := by
  intro p hp
  have hp' : p = (0, 1) := Finset.mem_singleton.mp hp
  subst p
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change (0 : Fin (d + 2)) < 1; norm_num⟩, ?_⟩
  intro q hq hlt
  have hq' := (Finset.mem_filter.mp hq).2
  rcases Prod.Lex.toLex_lt_toLex.mp hlt with hr | ⟨hr, hc⟩
  · exfalso
    change q.1 < (0 : Fin (d + 2)) at hr
    exact (Fin.not_lt_zero q.1) hr
  · exfalso
    have hv := congrArg Fin.val hr
    fin_omega

lemma adjacent_first_pivots (d : ℕ) :
    PivotsFromPattern ({((0 : Fin (d + 2)), (1 : Fin (d + 2)))} :
      Finset (Fin (d + 2) × Fin (d + 2))) {0} := by
  intro a ha
  have ha' : a = 0 := Finset.mem_singleton.mp ha
  subst a
  exact ⟨1, Finset.mem_singleton_self _⟩

def adjacentFirstTail (d : ℕ) :
    EliminationChain ({((0 : Fin (d + 2)), (1 : Fin (d + 2)))} :
      Finset (Fin (d + 2) × Fin (d + 2))) {0} :=
  (exists_complete_elimination_chain_from_initial _ _
    (adjacent_first_initial d) (adjacent_first_pivots d)).choose

lemma adjacentFirstTail_final (d : ℕ) :
    (adjacentFirstTail d).finalEntries = allPositiveRoots (d + 2) :=
  (exists_complete_elimination_chain_from_initial _ _
    (adjacent_first_initial d) (adjacent_first_pivots d)).choose_spec

lemma exists_adjacent_first_weights (d : ℕ) :
    ∃ ell : Fin (d + 2) → ℝ, (∑ i, ell i) = 0 ∧ ell 0 = ell 1 ∧
      ∀ p ∈ allPositiveRoots (d + 2), p ≠ (0, 1) → ell p.1 < ell p.2 := by
  refine ⟨centerWeights (d + 1) (midpointRootRaw 0 1), centerWeights_sum _ _, ?_, ?_⟩
  · unfold centerWeights
    rw [midpointRootRaw_equal]
  · intro p hp hne
    apply sub_neg.mp
    rw [centerWeights_sub]
    apply sub_neg.mpr
    apply midpointRootRaw_strict (by norm_num : (0 : Fin (d + 2)) < 1) (Finset.mem_filter.mp hp).2
    · have hp' := (Finset.mem_filter.mp hp).2
      have hnat : p.1.val + 1 ≤ p.2.val := by fin_omega
      have hreal : (p.1.val : ℝ) + 1 ≤ p.2.val := by exact_mod_cast hnat
      norm_num
      linarith
    · intro h
      exact hne (Prod.ext h.1 h.2)

end DukePrimeDegree

end

end OAI
