import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet
namespace TransferContracts

open Finset Set Pivots MainAlgorithm

section Pivots

variable {α : Type*} {r q n : ℕ}

/-- An injectively timed sequence determines one recorded pivot-mark vector. -/
lemma recordsPivots_unique (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (htime : Function.Injective time) (oldMark : Fin r → Bool)
    (movableMark : Fin q → Bool) {t u : Finset (Fin n)}
    (ht : RecordsPivots M label test time oldMark movableMark t)
    (hu : RecordsPivots M label test time oldMark movableMark u) : t = u := by
  ext f
  obtain ⟨o, ho, hto⟩ := ht f
  obtain ⟨p, hp, hup⟩ := hu f
  have hop := pivot_unique M label time htime ho hp
  subst p
  exact hto.symm.trans hup

variable [Fintype α]

/-- Complete marked-pivot contract: arbitrary repeated/redundant old labels,
all placements/orders/marks of at most `s` movable occurrences, and the exact
binomial bound. Source old-spanning/nonloop assumptions ensure every permitted
interleaving actually contributes exactly one vector. No positivity assumption
on `s`, `q`, `r`, or `n` is imposed. -/
theorem marked_pivot_contract (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (s : ℕ) (hqs : q ≤ s)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E)
    (holdspan : M.closure (oldPrefix b r) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅) :
    (markedPivotPatterns M b a test oldMark).card ≤
        4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k ∧
      ∀ (time : Occurrence r q → ℕ), OldOrdered time → Function.Injective time →
        ∀ movableMark : Fin q → Bool,
          ∃! t, t ∈ markedPivotPatterns M b a test oldMark ∧
            RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t := by
  refine ⟨card_markedPivotPatterns_le M b a test oldMark s hqs hground, ?_⟩
  intro time horder htime movableMark
  obtain ⟨t, htmem, ht⟩ := recorded_pattern_exists_of_old_spanning M b a test oldMark
    holdspan htest time horder htime movableMark
  refine ⟨t, ⟨htmem, ht⟩, ?_⟩
  intro u hu
  exact recordsPivots_unique M (occurrenceLabel b a) test time htime oldMark movableMark hu.2 ht

end Pivots

section Transfer

variable {n : ℕ}

/-- The independent comparison group is constructed by priority greedy and
fair-mask deletion, exactly as in the manuscript (`Y_i = (I* \ H) ∩ U_i`). -/
lemma comparison_group_indep_subset (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (a : Fin n → Option ℤ) (i : ℤ) :
    let Y := (positiveGreedy M a \ d.H).filter (fun e => a e = some i)
    M.Indep (Y : Set (Fin n)) ∧ (Y : Set (Fin n)) ⊆ (trueGroup M d a i : Set (Fin n)) := by
  classical
  dsimp only
  constructor
  · exact (positiveGreedy_survivors_indep M hE a d.H).subset (Finset.filter_subset _ _)
  · intro e he
    obtain ⟨heY, hei⟩ := Finset.mem_filter.mp he
    apply (mem_trueGroup M d a i e).mpr
    refine ⟨?_, hei⟩
    exact (Finset.mem_filter.mp (positiveGreedy_survivors_subset M a d.H heY)).2

/-- Full sample-to-rank inequality for the actual rounded weight vector.
`withMasks` averages all density, guard and test bits while fixing `H`;
`fairParityExpectation` averages parity. `listedRankStatistic` is explicitly
zero on the unlisted branch. Thus there is no conditioning on listing and no
independence assumption about the selected residual. -/
theorem sample_to_rank_contract (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (d : MainMasks n) (i : ℤ)
    (hn : densityThreshold ≤
      ((trueGroup M d (fun e => roundedLevel weightBase (w e)) i).card : ℝ)) :
    let a := fun e => roundedLevel weightBase (w e)
    let Y := (positiveGreedy M a \ d.H).filter (fun e => a e = some i)
    (retainedFraction * (Y.card : ℝ) - ((2 : ℝ) ^ 23)⁻¹ *
      (trueGroup M d a i).card) / densityThreshold ≤
      tripleMaskExpectation (fun _ => (1 : ℝ) / 4)
        (fun _ => thinningRate) (fun _ => thinningRate) Finset.univ
        (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2 ^ 100) (withMasks d D C T) a i
            (boolParity p) : ℝ))) := by
  classical
  let a := fun e => roundedLevel weightBase (w e)
  let Y := (positiveGreedy M a \ d.H).filter (fun e => a e = some i)
  have hY := comparison_group_indep_subset M hE d a i
  have h := listedRankStatistic_lower M hE d a i (Y : Set (Fin n)) hY.2 hY.1 hn
  simpa only [Set.ncard_coe_finset] using h

end Transfer

end TransferContracts
end MatroidProphet

end OAI
