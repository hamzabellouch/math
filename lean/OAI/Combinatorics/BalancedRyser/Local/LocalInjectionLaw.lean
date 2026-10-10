import OAI.Combinatorics.BalancedRyser.Local.AlignedUnusedLaw
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedEventMean

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_bind_probability_eq_mean {I Ω : Type*} [Fintype I] [Nonempty I]
    (ν : I → PMF Ω) (E : I × Ω → Prop) :
    (((PMF.uniformOfFintype I).bind (fun i => (ν i).map (fun ω => (i, ω)))).toOuterMeasure
      {z | E z}).toReal =
      (∑ i, ((ν i).toOuterMeasure {ω | E (i, ω)}).toReal) / Fintype.card I := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, PMF.toOuterMeasure_map_apply]
    rw [← Finset.mul_sum]
    simp only [Set.preimage_ofPred_eq]
    ring
  · intro i _
    apply ENNReal.mul_ne_top ((PMF.uniformOfFintype I).apply_ne_top i)
    rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Field F] [DecidableEq F] in

theorem nonempty_tokenInjections_of_budget (hbudget : 5 * b ≤ Fintype.card F + 1) :
    Nonempty (DirectionToken b κ ↪ Direction F) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [DirectionToken, Fintype.card_sum, Fintype.card_fin,
    Direction, Fintype.card_option]
  omega

omit [Field F] [DecidableEq F] in
theorem nonempty_tokenInjections_of_ten_budget (hbudget : 10 * b ≤ Fintype.card F) :
    Nonempty (DirectionToken b κ ↪ Direction F) :=
  nonempty_tokenInjections_of_budget (by omega)

def injectionAlignedLaw (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (bits : Bits b) (p : Point F) [Nonempty (DirectionToken b κ ↪ Direction F)] :
    PMF ((DirectionToken b κ ↪ Direction F) × MergedPairs F) :=
  (PMF.uniformOfFintype (DirectionToken b κ ↪ Direction F)).bind (fun e =>
    (AlignedUnused.alignedLaw P hκ (tokenInjectionEquiv F b κ e).1
      (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p).map
        (fun M => (e, M)))

theorem mem_support_injectionAlignedLaw
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (z : (DirectionToken b κ ↪ Direction F) × MergedPairs F) :
    z ∈ (injectionAlignedLaw P hκ bits p).support ↔
      Aligned P (tokenInjectionEquiv F b κ z.1).1 bits p z.2 := by
  unfold injectionAlignedLaw
  rw [PMF.mem_support_bind_iff]
  constructor
  · rintro ⟨e, _, hz⟩
    obtain ⟨M, hM, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    exact (PMF.mem_support_filter_iff _).mp hM |>.1
  · intro hz
    refine ⟨z.1, PMF.mem_support_uniformOfFintype _, ?_⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨z.2, ?_, rfl⟩
    exact (PMF.mem_support_filter_iff _).mpr
      ⟨hz, PMF.mem_support_uniformOfFintype _⟩

theorem injectionAverage_eq_injectionAlignedLaw
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) :
    injectionAverage P bits p E =
      ((injectionAlignedLaw P hκ bits p).toOuterMeasure
        {z | E (tokenInjectionEquiv F b κ z.1).1 z.2}).toReal := by
  unfold injectionAlignedLaw
  rw [uniform_bind_probability_eq_mean]
  unfold injectionAverage
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact AlignedUnused.conditionedOffsetProbability_eq_alignedLaw P hκ _
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p _

theorem injectionAverage_le_joint_probability
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (bits : Bits b) (p : Point F)
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (E : DirectionAssignment F b κ → MergedPairs F → Prop)
    (G : (DirectionToken b κ ↪ Direction F) × MergedPairs F → Prop)
    (h : ∀ e M, Aligned P (tokenInjectionEquiv F b κ e).1 bits p M →
      E (tokenInjectionEquiv F b κ e).1 M → G (e, M)) :
    injectionAverage P bits p E ≤
      ((injectionAlignedLaw P hκ bits p).toOuterMeasure {z | G z}).toReal := by
  rw [injectionAverage_eq_injectionAlignedLaw P hκ]
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro z hz
    exact h z.1 z.2 ((mem_support_injectionAlignedLaw P hκ bits p z).mp hz.2) hz.1

theorem injectionAverage_le_one
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) :
    injectionAverage P bits p E ≤ 1 := by
  cases isEmpty_or_nonempty (DirectionToken b κ ↪ Direction F) with
  | inl h =>
    let := h
    simp [injectionAverage]
  | inr h =>
    let := h
    rw [injectionAverage_eq_injectionAlignedLaw P hκ]
    have hone : (injectionAlignedLaw P hκ bits p).toOuterMeasure Set.univ = 1 :=
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)
    have hle : (injectionAlignedLaw P hκ bits p).toOuterMeasure
        {z | E (tokenInjectionEquiv F b κ z.1).1 z.2} ≤
        (injectionAlignedLaw P hκ bits p).toOuterMeasure Set.univ :=
      (injectionAlignedLaw P hκ bits p).toOuterMeasure.mono
        (Set.subset_univ {z : (DirectionToken b κ ↪ Direction F) × MergedPairs F | E (tokenInjectionEquiv F b κ z.1).1 z.2})
    rw [hone] at hle
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

end
end Balanced.Local.UsedEventUnion

end OAI
