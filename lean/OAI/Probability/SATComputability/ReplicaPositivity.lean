import OAI.Probability.SATComputability.SignMoment
import OAI.Probability.SATComputability.InterpolationInputs
import OAI.Probability.DilutedSpin.RawPatternIdentity

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PositiveInterpolation
open scoped BigOperators NNReal

theorem satModel_rawMoment {n : ℕ} (a : ℝ≥0) (β : ℝ)
    (P : Fin 3 → FiniteLaw (Fin n → Spin)) :
    rawReplicaMoment (satModel a β) P =
      (1 - Real.exp (-β)) ^ n * ∏ l, signFeature (P l) := by
  rw [rawReplicaMoment_eq_product]
  change (∫ z : InteractionSample 3, (-z.2.2.1)^n *
      ∏ l, (P l).expect (fun s => ∏ i, z.2.2.2 l (s i))
      ∂Measure.map (satSample β) signLaw.toMeasure) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    (by unfold FiniteLaw.expect; fun_prop)]
  simp only [satSample, neg_sub]
  rw [integral_const_mul]
  rw [signLaw_product (fun l J => (P l).expect (fun s => ∏ i, literalFactor J (s i)))]
  rfl

theorem satModel_raw_nonnegative {n : ℕ} (a : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β)
    (j : Fin 3) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ rawReplicaMoment (satModel a β) (fun _ : Fin 3 => P) -
      (3 : ℝ) * rawReplicaMoment (satModel a β) (fun l => if l = j then P else B) +
      (2 : ℝ) * rawReplicaMoment (satModel a β) (fun _ : Fin 3 => B) := by
  rw [satModel_rawMoment, satModel_rawMoment, satModel_rawMoment]
  exact signFeature_cubic_nonnegative hβ j P B

theorem satModel_interpolation_admissible {a : ℝ≥0} (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) : InterpolationAdmissible (satModel a β) := by
  refine ⟨by norm_num, ha, satModel_interaction_integrable a hβ.le,
    satModel_field_integrable a β, ?_, satModel_independent a β,
    satModel_identically_distributed a β, ?_, ?_, ?_, ?_⟩
  · filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    refine ⟨by norm_num [satSample], fun s => ?_⟩
    exact ⟨satSample_factorization β J s, satSample_product_bound hβ J s⟩
  · apply (indepFun_const_left (Real.exp (-β) - 1)
      (fun z : InteractionSample 3 => z.2.2.2)).congr
    · filter_upwards [satModel_supported a β] with z hz
      obtain ⟨J, rfl⟩ := hz
      rfl
    · rfl
  · intro n _
    apply (integrable_const ((1 - Real.exp (-β)) ^ n)).congr
    filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    simp [satSample]
  · intro n _
    apply integral_nonneg_of_ae
    filter_upwards [satModel_supported a β] with z hz
    obtain ⟨J, rfl⟩ := hz
    change 0 ≤ (-(Real.exp (-β) - 1)) ^ n
    apply pow_nonneg
    have he : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · intro n _ j P B
    exact satModel_raw_nonnegative a hβ.le j P B

end FixedClauseThreshold.Computability

end OAI
