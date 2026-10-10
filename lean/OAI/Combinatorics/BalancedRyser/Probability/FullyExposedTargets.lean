import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment
import OAI.Combinatorics.BalancedRyser.Probability.GeneratorEnumeration

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SuccessfulPositions (p : Fin 4 → Point F) (g : Direction F) : Prop :=
  (∃ c, ∀ i, OnLine (p i) (g, c)) ∧ Function.Injective p

omit [Fintype F] [DecidableEq F] in
theorem successfulPositions_unique_line (p : Fin 4 → Point F)
    (hp : Function.Injective p) (l m : Line F)
    (hl : ∀ i, OnLine (p i) l) (hm : ∀ i, OnLine (p i) m) : l = m := by
  exact eq_of_two_common_points (p 0) (p 1)
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (hp h))
    l m (hl 0) (hl 1) (hm 0) (hm 1)

omit [Fintype F] [DecidableEq F] in
theorem successfulPositions_unique_target (p : Fin 4 → Point F)
    {g h : Direction F} (hg : SuccessfulPositions p g)
    (hh : SuccessfulPositions p h) : g = h := by
  obtain ⟨⟨c, hc⟩, hp⟩ := hg
  obtain ⟨⟨d, hd⟩, _⟩ := hh
  exact congrArg Prod.fst (successfulPositions_unique_line p hp (g, c) (h, d) hc hd)

omit [DecidableEq F] in
theorem successfulPositions_target_card_le_one (p : Fin 4 → Point F) :
    (Finset.univ.filter (SuccessfulPositions p)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro g hg h hh
  exact successfulPositions_unique_target p (Finset.mem_filter.mp hg).2
    (Finset.mem_filter.mp hh).2

omit [Fintype F] [DecidableEq F] in
theorem tuplePoint_eq_of_generator_agreement (T : FourTuple F)
    {M a : MergedPairs F} (h : ∀ i, M (T.generator i) = a (T.generator i)) :
    tuplePoint M T = tuplePoint a T := by
  funext i
  simp only [tuplePoint, constituent, h i, h (i + 1)]

omit [Fintype F] [DecidableEq F] in
theorem tuplePoint_eq_of_fully_exposed (T : FourTuple F)
    (D : Finset (Direction F)) (a M : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D)
    (hM : ∀ d, d ∈ D → M d = a d) : tuplePoint M T = tuplePoint a T :=
  tuplePoint_eq_of_generator_agreement T (fun i => hM _ (hT i))

theorem fully_exposed_tuplePoint_law (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) :
    ((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).map
        (fun M => tuplePoint M T) = PMF.pure (tuplePoint a T) := by
  simp only [PartialAlignment.offsetLaw_eq_uniform]
  rw [ConditionalRestriction.uniform_fixed_filter, PMF.map_comp]
  have hf : (fun M : ConditionalRestriction.FixedArray (fun d => d ∈ D) a =>
      tuplePoint M.1 T) = Function.const _ (tuplePoint a T) := by
    funext M
    exact tuplePoint_eq_of_fully_exposed T D a M.1 hT M.2
  simp only [Function.comp_def]
  rw [hf, PMF.map_const]

theorem fully_exposed_success_probability (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) (g : Direction F) :
    (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
      (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
        {M | SuccessfulPositions (tuplePoint M T) g}).toReal =
      if SuccessfulPositions (tuplePoint a T) g then 1 else 0 := by
  have h := congrArg (fun law : PMF (Fin 4 → Point F) =>
    (law.toOuterMeasure {p | SuccessfulPositions p g}).toReal)
      (fully_exposed_tuplePoint_law T D a hT)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply] at h
  simpa only [Set.mem_ofPred_eq, Set.preimage_ofPred_eq, apply_ite,
    ENNReal.toReal_one, ENNReal.toReal_zero] using h

theorem sum_fully_exposed_success_probability_le_one (T : FourTuple F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hT : ∀ i, T.generator i ∈ D) :
    (∑ g : Direction F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
          {M | SuccessfulPositions (tuplePoint M T) g}).toReal) ≤ 1 := by
  simp_rw [fully_exposed_success_probability T D a hT]
  have hcard := successfulPositions_target_card_le_one (tuplePoint a T)
  have hsum : (∑ g : Direction F,
      if SuccessfulPositions (tuplePoint a T) g then (1 : ℝ) else 0) =
      ((Finset.univ.filter (SuccessfulPositions (tuplePoint a T))).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero]
  rw [hsum]
  exact_mod_cast hcard

omit [Field F] in
theorem generators_exposed_of_code_oldCount_four (D : Finset (Direction F))
    (c : (Fin 4 → Direction F) × (Fin 4 → Bool))
    (hc : c ∈ tupleCodesWithOldCount D 4) : ∀ i, c.1 i ∈ D := by
  have hcard := (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
  have hfull : (Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ D)) = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ _).mp
    simpa only [Fintype.card_fin] using hcard
  intro i
  have hi : i ∈ Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ D) := by
    rw [hfull]
    exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hi).2

theorem sum_fully_exposed_code_success_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ c ∈ tupleCodesWithOldCount D 4, ∑ g : Direction F,
      (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
        (PartialAlignment.canonical_exposure_supported D a)).toOuterMeasure
          {M | SuccessfulPositions (tuplePoint M ⟨c.1, c.2⟩) g}).toReal) ≤
      16 * (D.card : ℝ) ^ 4 := by
  calc
    _ ≤ ∑ _c ∈ tupleCodesWithOldCount D 4, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact sum_fully_exposed_success_probability_le_one ⟨c.1, c.2⟩ D a
        (generators_exposed_of_code_oldCount_four D c hc)
    _ = ((tupleCodesWithOldCount D 4).card : ℝ) := by simp
    _ ≤ 16 * (D.card : ℝ) ^ 4 := by
      have hcount : (tupleCodesWithOldCount D 4).card ≤ 16 * D.card ^ 4 := by
        simpa using card_tupleCodesWithOldCount_le D 4
      exact_mod_cast hcount

end
end Balanced.TupleAlignment

end OAI
