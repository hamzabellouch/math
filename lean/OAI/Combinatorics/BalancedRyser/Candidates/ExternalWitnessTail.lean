import OAI.Combinatorics.BalancedRyser.Candidates.CandidateAbundanceAssembly
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExternalTransport
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel
import OAI.Combinatorics.BalancedRyser.Probability.ProbabilityPerturbation

namespace OAI

namespace Balanced.ExternalWitnessTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidateExposure ExternalAssembly

section FiniteMarkov
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

private theorem power_tail_le (p : PMF Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (t : ℝ) (ht : 0 < t) (s : ℕ) :
    p.toMeasure.real {x | t ≤ f x} ≤ (∫ x, f x ^ s ∂p.toMeasure) / t ^ s := by
  have hsub : {x | t ≤ f x} ⊆ {x | t ^ s ≤ f x ^ s} :=
    fun x hx => pow_le_pow_left₀ ht.le hx s
  have hm := measureReal_mono (μ := p.toMeasure) hsub
  have hk := mul_meas_ge_le_integral_of_nonneg
    (μ := p.toMeasure) (f := fun x => f x ^ s)
    (Filter.Eventually.of_forall fun x => pow_nonneg (hf x) s)
    Integrable.of_finite (t ^ s)
  apply (le_div_iff₀ (pow_pos ht s)).mpr
  exact (mul_le_mul_of_nonneg_right hm (pow_pos ht s).le).trans
    (by simpa only [mul_comm] using hk)
end FiniteMarkov

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤
local instance : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem single_direction_tail_le (B : ℝ) (g : Direction F)
    (hmoment : (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw F).toMeasure) ≤ B) :
    offsetEventProbability {M : MergedPairs F |
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ ((witnesses g M).card : ℝ)} ≤
      B / (Fintype.card F : ℝ)^4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := power_tail_le (offsetLaw F) (fun M => ((witnesses g M).card : ℝ))
    (fun _ => Nat.cast_nonneg _) ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
    (Real.rpow_pos_of_pos hq _) 400
  have hp : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ (400 : ℕ) =
      (Fintype.card F : ℝ)^4 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [hp] at h
  have hr (E : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real E =
      offsetEventProbability E := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
      (Set.to_countable _).measurableSet]
    rfl
  rw [hr] at h
  exact h.trans (div_le_div_of_nonneg_right hmoment (pow_pos hq 4).le)

theorem some_direction_tail_le (B : ℝ) (hB : 0 ≤ B)
    (hmoment : ∀ g : Direction F,
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw F).toMeasure) ≤ B) :
    offsetEventProbability {M : MergedPairs F | ∃ g : Direction F,
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      2 * B / (Fintype.card F : ℝ)^3 := by
  let E (g : Direction F) : Set (MergedPairs F) := {M |
    (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
      ((witnesses g M).card : ℝ)}
  have heq : {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} = ⋃ g, E g := by
    ext M
    simp
  have hr (A : Set (MergedPairs F)) : (offsetLaw F).toMeasure.real A =
      offsetEventProbability A := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
    rfl
  have hu := measureReal_iUnion_fintype_le (μ := (offsetLaw F).toMeasure) E
  simp_rw [hr] at hu
  change offsetEventProbability {M : MergedPairs F | ∃ g : Direction F, M ∈ E g} ≤ _
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ ∑ g : Direction F, offsetEventProbability (E g) := hu
    _ ≤ ∑ _g : Direction F, B / (Fintype.card F : ℝ)^4 := by
      apply Finset.sum_le_sum
      intro g _
      exact single_direction_tail_le B g (hmoment g)
    _ = ((Fintype.card F : ℝ) + 1) * (B / (Fintype.card F : ℝ)^4) := by
      simp [Direction, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (Fintype.card F : ℝ)) * (B / (Fintype.card F : ℝ)^4) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hq])
        (div_nonneg hB (pow_pos hq0 4).le)
    _ = _ := by field_simp

theorem tendsto_some_direction_tail (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hmoment : ∀ n (g : Direction (K n)),
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)}) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hz : Tendsto (fun n => 2 * B / (Fintype.card (K n) : ℝ)^3)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using
      ((tendsto_inv_atTop_zero.comp hreal).pow 3).const_mul (2 * B)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => some_direction_tail_le (F := K n) B hB (hmoment n)) hz

theorem candidateSlots_of_uniform_moment (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hmoment : ∀ n (g : Direction (K n)),
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∀ s, CandidateAbundanceAssembly.slotLinearConstant * Fintype.card (K n) ≤
        ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (K n)}) atTop (𝓝 1) := by
  apply CandidateAbundanceAssembly.tendsto_candidateSlots_of_external_tail K hq
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
    (tendsto_some_direction_tail B hB K hq hmoment)
  intro n
  apply pmf_outerReal_mono (offsetLaw (K n))
  rintro M ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hq1 : (1 : ℝ) ≤ Fintype.card (K n) := by
    exact_mod_cast Fintype.card_pos (α := K n)
  have hp : (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤ Fintype.card (K n) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
  exact hp.trans ((show (Fintype.card (K n) : ℝ) ≤
    ((CandidateValidityAssembly.externalFailures M g).card : ℝ) by
      exact_mod_cast le_of_lt hg).trans (Nat.cast_le.mpr
        (CandidateValidityAssembly.externalFailures_card_le_witnesses M g)))

end
end Balanced.ExternalWitnessTail

end OAI
