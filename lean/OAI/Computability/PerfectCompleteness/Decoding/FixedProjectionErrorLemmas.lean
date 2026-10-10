import OAI.Computability.PerfectCompleteness.Decoding.ChildFiniteCallCollisionTransfer
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison
import OAI.Computability.PerfectCompleteness.Reduction.FixedComparisonErrorsLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedProjectionError

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem sparse_error_lt {retained : Nat} (hcalls : retained ≤ calls p.plan)
    (height : Nat) :
    Real.sqrt ((1 + (projectionProbability p height : ℝ) ^ 2 *
      ((ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
        retained (rows p.plan) : ℝ) - 1)) ^ branch p height - 1) / 2 < p.accuracy := by
  let L : ℝ := ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
    retained (rows p.plan)
  let m : ℝ := p.cubeSize height
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (ChildBlockCardinality.shape_bound_pos (branch p) height
        (sourceLength p.plan hδ) retained (rows p.plan)))
  have hm4 : 0 ≤ m ^ 4 := by positivity
  have hbeta : (projectionProbability p height : ℝ) ^ 2 = 1 / m ^ 4 := by
    simp only [projectionProbability, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_natCast]
    dsimp only [m]
    ring
  have hbase : 1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1) ≤
      1 + L ^ 2 / m ^ 4 := by
    rw [hbeta]
    have hsq : L - 1 ≤ L ^ 2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_right hsq hm4
    calc
      1 + (1 / m ^ 4) * (L - 1) = 1 + (L - 1) / m ^ 4 := by ring
      _ ≤ 1 + L ^ 2 / m ^ 4 := by linarith
  have hnonneg : 0 ≤ 1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1) := by
    have : 0 ≤ L - 1 := by linarith
    positivity
  have h := (FixedComparisonErrors.comparison_errors p hcalls height).2.1
  change Real.sqrt ((1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1)) ^
    (p.cubeSize height ^ 3) - 1) / 2 < p.accuracy
  apply lt_of_le_of_lt _ h
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  exact sub_le_sub_right (pow_le_pow_left₀ hnonneg hbase _) 1

end
end PerfectCompleteness.FixedProjectionError

end

section

namespace PerfectCompleteness.FixedChildCollisionTransfer

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)

theorem posterior_error_lt {retained : Nat}
    (hcalls : retained ≤ calls parameters.plan) (height : Nat) :
    2 * ((projectionProbability parameters height : ℝ) *
      (ChildBlockCardinality.bound (branch parameters) height
        (sourceLength parameters.plan hδ) retained (rows parameters.plan) : ℝ) /
      (1 - (projectionProbability parameters height : ℝ))) < parameters.accuracy := by
  have h := (FixedComparisonErrors.comparison_errors parameters hcalls height).2.2
  simpa only [projectionProbability, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast] using h

theorem lower_pair_calls_le {n height : Nat}
    (path : Path (branch parameters) n (height + 1)) (hn : n ≤ parameters.plan.depth) :
    Fintype.card (Option
      (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path)) ≤
      calls parameters.plan := by
  have h := FixedCallBudget.modified_calls_le (rows parameters.plan)
    (repeats parameters.plan) path hn
  rw [Fintype.card_option]
  unfold calls
  omega

variable {height : Nat} {C : Type*} [Fintype C]
  {Z : Fin (branch parameters height) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_lt_uniform_full
    (hcalls : Fintype.card C ≤ calls parameters.plan)
    (slots : Slots (branch parameters) (height + 1) →
      Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
    (projected : (i : Fin (branch parameters height)) → Z i →
      Slots (branch parameters) height → Fin (sourceLength parameters.plan hδ) →
        MixedSupport.Slot)
    (projection : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch parameters height)) → FiniteDistribution (Z i))
    (F₀ F₁ : CutChildGrouping.Raw (C := C) slots (rows parameters.plan) →
      Option (ChildBilinearCollisionTransfer.ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildCallNumbering.Raw (C := C) (rows parameters.plan) (childSlots slots i)))
        (ChildCallNumberingLaws.replacementLaws (C := C) (rows parameters.plan)
          (childSlots slots) projected projection choiceLaw)
        (projectionProbability parameters height : ℝ)
        (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
        (by exact_mod_cast (projectionProbability_bounds parameters height).2.le)).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) <
      (CutChildGrouping.rawLaw (C := C) slots (rows parameters.plan)).probability
        (fun raw => BilinearCollisionTransfer.fullCollision (F₀ raw) (F₁ raw)) +
          2 * parameters.accuracy := by
  have hβ : 0 ≤ (projectionProbability parameters height : ℝ) := by
    exact_mod_cast (projectionProbability_bounds parameters height).1.le
  have hβ' : (projectionProbability parameters height : ℝ) < 1 := by
    exact_mod_cast (projectionProbability_bounds parameters height).2
  have htransfer := ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full
    (C := C) (rows parameters.plan) slots projected projection choiceLaw
    (projectionProbability parameters height : ℝ) hβ hβ' F₀ F₁
  have hposterior := posterior_error_lt parameters hcalls height
  have hvariation := FixedProjectionError.sparse_error_lt parameters hcalls height
  change _ < (FiniteProduct.law (fun i => FiniteDistribution.uniform
    (ChildCallNumbering.Raw (C := C) (rows parameters.plan) (childSlots slots i)))).probability
      (fun raw => BilinearCollisionTransfer.fullCollision (F₀ raw) (F₁ raw)) +
        2 * parameters.accuracy
  linarith

end
end PerfectCompleteness.FixedChildCollisionTransfer

end

end OAI
