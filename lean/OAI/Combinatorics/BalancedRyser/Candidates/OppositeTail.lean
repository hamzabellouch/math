import OAI.Combinatorics.BalancedRyser.Candidates.OppositeAssembly
import OAI.Combinatorics.BalancedRyser.Probability.ProbabilityPerturbation

namespace OAI

namespace Balanced.OppositeTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidateExposure OppositeAssembly

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

theorem exposedLaw_empty (a : MergedPairs F) : exposedLaw ∅ a = offsetLaw F := by
  apply PMF.ext
  intro M
  simp [exposedLaw, PMF.filter_apply]
  rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  simp

theorem conditional_witness_tail_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) (t : ℝ) (ht : 0 < t) :
    ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((witnesses g M).card : ℝ)}).toReal ≤
      (meanBound (m + (s - 1) * 5))^s / t^s := by
  have h := power_tail_le (exposedLaw old a)
    (fun M => ((witnesses g M).card : ℝ)) (fun _ => Nat.cast_nonneg _)
    t ht s
  have he := witnesses_moment_le g old a m s hm
  rw [PMF.integral_eq_sum] at h
  simp only [smul_eq_mul] at h
  have hreal : (exposedLaw old a).toMeasure.real
      {M | t ≤ ((witnesses g M).card : ℝ)} =
      ((exposedLaw old a).toOuterMeasure
      {M | t ≤ ((witnesses g M).card : ℝ)}).toReal := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]
  rw [hreal] at h
  exact h.trans (div_le_div_of_nonneg_right he (pow_pos ht s).le)

def tailConstant : ℝ := (meanBound ((300 - 1) * 5))^300

theorem single_direction_tail_le (g : Direction F) :
    offsetEventProbability {M : MergedPairs F |
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      tailConstant / (Fintype.card F : ℝ)^3 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := conditional_witness_tail_le g ∅ (fun _ _ => (0 : F)) 0 300
    (by simp) ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) (Real.rpow_pos_of_pos hq _)
  rw [exposedLaw_empty] at h
  have hp : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ (300 : ℕ) =
      (Fintype.card F : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  rw [hp] at h
  simpa only [offsetEventProbability, tailConstant, Nat.zero_add] using h

theorem some_direction_tail_le :
    offsetEventProbability {M : MergedPairs F | ∃ g : Direction F,
      (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)} ≤
      2 * tailConstant / (Fintype.card F : ℝ)^2 := by
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
  have hB : 0 ≤ tailConstant := by unfold tailConstant; exact pow_nonneg (meanBound_nonneg _) _
  calc
    _ ≤ ∑ g : Direction F, offsetEventProbability (E g) := hu
    _ ≤ ∑ _g : Direction F, tailConstant / (Fintype.card F : ℝ)^3 := by
      apply Finset.sum_le_sum
      intro g _
      exact single_direction_tail_le g
    _ = ((Fintype.card F : ℝ) + 1) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      simp [Direction, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (Fintype.card F : ℝ)) * (tailConstant / (Fintype.card F : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hq])
        (div_nonneg hB (pow_pos hq0 3).le)
    _ = _ := by field_simp

theorem tendsto_some_direction_tail
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
        ((witnesses g M).card : ℝ)}) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hz : Tendsto (fun n => 2 * tailConstant / (Fintype.card (K n) : ℝ)^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using
      ((tendsto_inv_atTop_zero.comp hreal).pow 2).const_mul (2 * tailConstant)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => some_direction_tail_le (F := K n)) hz

theorem tendsto_all_directions_small
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∀ g : Direction (K n), ((witnesses g M).card : ℝ) <
        (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ)}) atTop (𝓝 1) := by
  have hbad := tendsto_some_direction_tail K hq
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  have heq (n : ℕ) : offsetEventProbability {M : MergedPairs (K n) |
      ∀ g : Direction (K n), ((witnesses g M).card : ℝ) <
        (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ)} =
      1 - offsetEventProbability {M : MergedPairs (K n) |
        ∃ g : Direction (K n), (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤
          ((witnesses g M).card : ℝ)} := by
    have hs : {M : MergedPairs (K n) | ∀ g : Direction (K n),
        ((witnesses g M).card : ℝ) < (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ)} =
        {M : MergedPairs (K n) | ∃ g : Direction (K n),
          (Fintype.card (K n) : ℝ) ^ (1 / 100 : ℝ) ≤ ((witnesses g M).card : ℝ)}ᶜ := by
      ext M
      simp
    rw [hs]
    exact pmf_outerReal_compl _ _
  simpa only [sub_zero,← heq] using h

end
end Balanced.OppositeTail

end OAI
