import OAI.Combinatorics.BalancedRyser.Candidates.CandidateProbabilityAssembly
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceTests
import OAI.Combinatorics.BalancedRyser.Probability.PatternTailAsymptotics
import OAI.Combinatorics.BalancedRyser.Probability.RootPatternModel

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

local instance incidenceMeasurableSpace : MeasurableSpace F := ⊤

theorem small_test_tail_le (t : Test F) (C : ℝ)
    (hmom : (∫ M : MergedPairs F, (count M t : ℝ) ^ 500
      ∂(offsetLaw F).toMeasure) ≤ C) :
    (offsetLaw F).toMeasure.real
      {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)} ≤
        C / (Fintype.card F : ℝ) ^ 5 := by
  let P := TupleAlignment.rootPatternModel (none : Direction F)
  let x : MergedPairs F := fun _ _ => 0
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ^ 500 =
      (Fintype.card F : ℝ) ^ 5 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have h := PatternTails.fixed_tail_le_moment P ∅ x
    (fun M => (count M t : ℝ)) (measurable_of_finite _)
    (fun _ => Nat.cast_nonneg _) (Fintype.card (SplitChoice F))
    (fun M => by exact_mod_cast count_le M t)
    ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
    (Real.rpow_pos_of_pos hq _) 500
  simp only [PatternModel.fixedExpectation] at h
  rw [TupleAlignment.rootPatternModel_measure] at h
  exact (h.trans (div_le_div_of_nonneg_right hmom (by positivity))).trans_eq
    (by rw [hpow])

theorem small_bad_probability_le (C : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ t : Test F, (∫ M : MergedPairs F, (count M t : ℝ) ^ 500
      ∂(offsetLaw F).toMeasure) ≤ C) :
    offsetEventProbability (F := F)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)))} ≤
        15 * C / Fintype.card F := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card (Test F) : ℝ) ≤ 15 * (Fintype.card F : ℝ) ^ 4 := by
    exact_mod_cast card_test_le (F := F)
  have hu := PatternTails.polynomial_union_tail_le (offsetLaw F).toMeasure
    (fun t : Test F =>
      {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)})
    (Fintype.card F) hq 4 1 15 C hC hc (fun t => small_test_tail_le t C (hmom t))
  have hsub : {M : MergedPairs F |
      ¬ SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)))} ⊆
      ⋃ t : Test F,
        {M | (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)} := by
    intro M hM
    obtain ⟨t, ht⟩ := not_forall.mp hM
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    have hn : Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)) ≤ count M t :=
      Nat.le_of_lt (Nat.lt_of_not_ge ht)
    change (Fintype.card F : ℝ) ^ (1 / 100 : ℝ) ≤ (count M t : ℝ)
    exact (Nat.le_ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))).trans
      (by exact_mod_cast hn)
  unfold offsetEventProbability
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite _).measurableSet]
  exact (measureReal_mono hsub).trans (by simpa only [pow_one] using hu)

theorem tendsto_smallGood_of_moments
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hmom : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t : Test (F n),
      (∫ M : MergedPairs (F n), (count M t : ℝ) ^ 500
        ∂(offsetLaw (F n)).toMeasure) ≤ C) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1) := by
  obtain ⟨C, hC, hmom⟩ := hmom
  have hbad : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    · filter_upwards [hmom] with n hn
      exact small_bad_probability_le C hC hn
    · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hq).const_mul
          (15 * C)
  have hp (n : ℕ) : offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))} =
      1 - offsetEventProbability (F := F n)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))} := by
    simpa only [Set.compl_ofPred, not_not, offsetEventProbability] using
      pmf_outerReal_compl (offsetLaw (F n))
        {M | ¬ SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))}
  simp_rw [hp]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

end Balanced.CandidateIncidenceTests

end

end OAI
