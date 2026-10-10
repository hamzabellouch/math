import OAI.Combinatorics.BalancedRyser.Candidates.CandidateHighMoments

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance candidateAbundanceMeasurableSpace : MeasurableSpace F := ⊤

theorem successfulTupleCount_lower_tail (g : Direction F) (hq : 24 ≤ Fintype.card F) :
    (offsetLaw F).toMeasure.real {M | successfulTupleCount g M < 8 * Fintype.card F} ≤
      centeredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 := by
  let q : ℝ := Fintype.card F
  let μ := (offsetLaw F).toMeasure
  let b : ℝ := ∫ M, (successfulTupleCount g M : ℝ) ∂μ
  have hq0 : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hb : 9*q ≤ b := by
    dsimp [b, μ, q]
    rw [integral_successfulTupleCount_original]
    exact rootMean_lower_bound _ hq
  have hsub : {M | successfulTupleCount g M < 8 * Fintype.card F} ⊆
      {M | q^4 ≤ |(successfulTupleCount g M : ℝ) - b|^4} := by
    intro M hM
    have hh : (successfulTupleCount g M : ℝ) < 8*q := by
      change successfulTupleCount g M < 8 * Fintype.card F at hM
      dsimp [q]
      exact_mod_cast hM
    have hd : q ≤ |(successfulTupleCount g M : ℝ) - b| := by
      rw [abs_sub_comm]
      exact (show q ≤ b - (successfulTupleCount g M : ℝ) by linarith).trans (le_abs_self _)
    exact pow_le_pow_left₀ hq0.le hd 4
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun M => |(successfulTupleCount g M : ℝ) - b|^4)
    (Filter.Eventually.of_forall (fun _ => by positivity)) Integrable.of_finite (q^4)
  have hmoment : (∫ M, |(successfulTupleCount g M : ℝ) - b|^4 ∂μ) ≤
      centeredMomentConstant 0 2 * q^2 := by
    simpa only [b, μ, q] using successfulTupleCount_centered_moment_le g 2
  have hbound : q^4 * μ.real {M | successfulTupleCount g M < 8 * Fintype.card F} ≤
      centeredMomentConstant 0 2 * q^2 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hm.trans hmoment)
  change μ.real _ ≤ centeredMomentConstant 0 2 / q^2
  calc
    _ ≤ (centeredMomentConstant 0 2 * q^2) / q^4 := by
      apply (le_div_iff₀ (pow_pos hq0 4)).mpr
      simpa only [mul_comm] using hbound
    _ = centeredMomentConstant 0 2 / q^2 := by
      field_simp

theorem successfulTupleCount_any_lower_tail (hq : 24 ≤ Fintype.card F) :
    (offsetLaw F).toMeasure.real
      {M | ∃ g : Direction F, successfulTupleCount g M < 8 * Fintype.card F} ≤
      2 * centeredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
  let E : Direction F → Set (MergedPairs F) :=
    fun g => {M | successfulTupleCount g M < 8 * Fintype.card F}
  have heq : {M | ∃ g : Direction F, successfulTupleCount g M < 8 * Fintype.card F} =
      ⋃ g, E g := by ext M; simp [E]
  rw [heq]
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  calc
    _ ≤ ∑ g : Direction F, (offsetLaw F).toMeasure.real (E g) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _g : Direction F, centeredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 :=
      Finset.sum_le_sum (fun g _ => successfulTupleCount_lower_tail g hq)
    _ = ((Fintype.card F : ℝ) + 1) *
        (centeredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      simp [Direction, Fintype.card_option]
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        (centeredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      gcongr
      · exact div_nonneg (centeredMomentConstant_nonneg 0 2) (by positivity)
      · linarith
    _ = 2 * centeredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
      field_simp

theorem successfulTupleCount_all_tendsto_one
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => (offsetLaw (F n)).toMeasure.real
      {M | ∀ g : Direction (F n), 8 * Fintype.card (F n) ≤ successfulTupleCount g M})
      atTop (𝓝 1) := by
  let bad : ℕ → ℝ := fun n => (offsetLaw (F n)).toMeasure.real
    {M | ∃ g : Direction (F n), successfulTupleCount g M < 8 * Fintype.card (F n)}
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  have hbound : Tendsto (fun n => 2 * centeredMomentConstant 0 2 /
      (Fintype.card (F n) : ℝ)) atTop (𝓝 0) :=
    hqR.const_div_atTop _
  have hbad : Tendsto bad atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) ?_ hbound
    filter_upwards [hcard.eventually (eventually_ge_atTop 24)] with n hn
    exact successfulTupleCount_any_lower_tail hn
  have hall : Tendsto (fun n => 1 - bad n) atTop (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hbad
  have heq (n : ℕ) : (offsetLaw (F n)).toMeasure.real
      {M | ∀ g : Direction (F n), 8 * Fintype.card (F n) ≤ successfulTupleCount g M} =
      1 - bad n := by
    have hset : {M | ∀ g : Direction (F n),
        8 * Fintype.card (F n) ≤ successfulTupleCount g M} =
        {M | ∃ g : Direction (F n), successfulTupleCount g M < 8 * Fintype.card (F n)}ᶜ := by
      ext M
      simp
    rw [hset, measureReal_compl (Set.toFinite _).measurableSet]
    simp only [probReal_univ, bad]
  simpa only [sub_zero, ← heq] using hall

end
end Balanced.CandidateExposure

end OAI
