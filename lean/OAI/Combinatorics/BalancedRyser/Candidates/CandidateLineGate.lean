import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposure
import OAI.Combinatorics.BalancedRyser.Probability.FiniteFixedLaw

namespace OAI

namespace Balanced.CandidateLineGate

noncomputable section
open scoped Classical BigOperators
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem not_mem_constituentLines_iff (M : MergedPairs F) (L : Line F) :
    L ∉ constituentLines M ↔ ∀ b : Bool, M L.1 b ≠ L.2 := by
  constructor
  · intro h b hb
    apply h
    apply Finset.mem_image.mpr
    refine ⟨(L.1, b), Finset.mem_univ _, ?_⟩
    exact Prod.ext rfl hb
  · intro h hL
    obtain ⟨⟨d, b⟩, _, heq⟩ := Finset.mem_image.mp hL
    have hd : d = L.1 := congrArg Prod.fst heq
    have hv : M d b = L.2 := congrArg Prod.snd heq
    exact h b (hd ▸ hv)

omit [Field F] in
theorem exposed_constituents_avoid (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F) (ha : L ∉ constituentLines a) :
    ∀ d ∈ D, ∀ b, constituent a d b ≠ L := by
  intro d _ b heq
  apply ha
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, heq⟩

omit [Field F] in
theorem not_mem_iff_of_direction_agreement (L : Line F) (M a : MergedPairs F)
    (h : M L.1 = a L.1) :
    L ∉ constituentLines M ↔ L ∉ constituentLines a := by
  rw [not_mem_constituentLines_iff, not_mem_constituentLines_iff, h]

theorem not_mem_iff_on_exposed_support (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F) (hL : L.1 ∈ D)
    (M : MergedPairs F) (hM : M ∈ (exposedLaw D a).support) :
    L ∉ constituentLines M ↔ L ∉ constituentLines a := by
  have hfix : ∀ d, d ∈ D → M d = a d :=
    (PMF.mem_support_filter_iff
      (PartialAlignment.canonical_exposure_supported D a)).mp hM |>.1
  exact not_mem_iff_of_direction_agreement L M a (hfix _ hL)

theorem conditionalProbability_gate (D : Finset (Direction F))
    (a : MergedPairs F) (L : Line F) (hL : L.1 ∈ D)
    (E : Set (MergedPairs F)) :
    conditionalProbability D a {M | L ∉ constituentLines M ∧ M ∈ E} =
      if L ∉ constituentLines a then conditionalProbability D a E else 0 := by
  by_cases ha : L ∉ constituentLines a
  · rw [ite_eq_left ha]
    unfold conditionalProbability
    congr 1
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext M
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · rintro ⟨hE, hM⟩
      exact ⟨⟨(not_mem_iff_on_exposed_support D a L hL M hM).mpr ha, hE⟩, hM⟩
  · rw [ite_eq_right ha]
    unfold conditionalProbability
    have hzero : (exposedLaw D a).toOuterMeasure
        {M | L ∉ constituentLines M ∧ M ∈ E} = 0 := by
      apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      apply Set.disjoint_left.mpr
      intro M hM hE
      exact ha ((not_mem_iff_on_exposed_support D a L hL M hM).mp hE.1)
    rw [hzero, ENNReal.toReal_zero]

omit [Field F] in
theorem not_mem_fixArray_iff (D : Finset (Direction F))
    (a M : MergedPairs F) (L : Line F) (hL : L.1 ∈ D) :
    L ∉ constituentLines
      (ConditionalRestriction.fixArray (fun d => d ∈ D) a M) ↔
      L ∉ constituentLines a := by
  apply not_mem_iff_of_direction_agreement
  simp [ConditionalRestriction.fixArray, hL]

omit [Field F] in
theorem gated_count_fixArray (D : Finset (Direction F))
    (a M : MergedPairs F) (L : Line F) (hL : L.1 ∈ D)
    (f : MergedPairs F → ℝ) :
    (if L ∉ constituentLines
        (ConditionalRestriction.fixArray (fun d => d ∈ D) a M)
      then f (ConditionalRestriction.fixArray (fun d => d ∈ D) a M) else 0) =
    if L ∉ constituentLines a
      then f (ConditionalRestriction.fixArray (fun d => d ∈ D) a M) else 0 := by
  simp only [not_mem_fixArray_iff D a M L hL]

end
end Balanced.CandidateLineGate

end OAI
