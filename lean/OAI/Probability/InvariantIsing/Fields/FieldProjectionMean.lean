import OAI.Probability.InvariantIsing.Fields.FieldProjectionLoss

namespace OAI

/-! Averaging the terminal loss requires only a field second moment and
the expected projection distance. The bound has no cascade-depth term. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma continuous_fieldCanonicalWeights {N : ℕ} (σ : Spin N) :
    Continuous (fun z : Fin N → ℝ => finiteCanonicalWeights (fieldEnergy z) σ) := by
  have hc (τ : Spin N) : Continuous (fun z : Fin N → ℝ => fieldEnergy z τ) := by
    unfold fieldEnergy
    fun_prop
  exact (Real.continuous_exp.comp (hc σ)).div
    (continuous_finsetSum _ (fun τ _ => Real.continuous_exp.comp (hc τ)))
    (fun z => (sum_exp_pos (fieldEnergy z)).ne')

lemma continuous_fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N) :
    Continuous (fieldProjectionDistance f) := by
  unfold fieldProjectionDistance
  exact continuous_finsetSum _ (fun σ _ => (continuous_fieldCanonicalWeights σ).mul_const _)

lemma fieldProjectionDistance_le {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) :
    fieldProjectionDistance f z ≤ N := by
  calc
    _ ≤ ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * N := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (finiteCanonicalWeights_pos _ σ).le
      exact_mod_cast (show hammingDist σ (f σ) ≤ N from
        hammingDist_le_card_fintype.trans_eq (Fintype.card_fin N))
    _ = _ := by rw [← Finset.sum_mul, finiteCanonicalWeights_sum, one_mul]

lemma integrable_fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fieldProjectionDistance f) μ := by
  apply (integrable_const (N : ℝ)).mono' (continuous_fieldProjectionDistance f).aestronglyMeasurable
  exact ae_of_all μ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fieldProjectionDistance_nonneg f z)]
    exact fieldProjectionDistance_le f z)

theorem field_projection_mean_loss {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (f : Spin N → Spin N) (hf : ∀ σ, f σ ∈ S)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hM : Integrable (fun z : Fin N → ℝ => ∑ i, z i ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ z, (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z ∂μ) ≤
      ε * (∫ z, ∑ i, z i ^ 2 ∂μ) +
      (ε⁻¹ + t) * (∫ z, fieldProjectionDistance f z ∂μ) +
      N * Real.log (1 + Real.exp (-t)) := by
  let L := fun z : Fin N → ℝ =>
    (∑ i, Real.log (Real.cosh (z i))) - restrictedFieldTerminal S z
  let B := fun z : Fin N → ℝ => ε * (∑ i, z i ^ 2) +
    (ε⁻¹ + t) * fieldProjectionDistance f z + N * Real.log (1 + Real.exp (-t))
  have hA : Integrable (fun z : Fin N → ℝ => ε * (∑ i, z i ^ 2)) μ := hM.const_mul ε
  have hD : Integrable (fun z => (ε⁻¹ + t) * fieldProjectionDistance f z) μ :=
    (integrable_fieldProjectionDistance f μ).const_mul (ε⁻¹ + t)
  have hB : Integrable B μ :=
    (hA.add hD).add (integrable_const _)
  have hLmeas : AEStronglyMeasurable L μ := by
    have hc := (continuous_restrictedFieldTerminal Finset.univ Finset.univ_nonempty).sub
      (continuous_restrictedFieldTerminal S hS)
    have heq : (restrictedFieldTerminal Finset.univ - restrictedFieldTerminal S) = L := by
      funext z
      change restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z = _
      rw [restrictedFieldTerminal_univ]
    rw [heq] at hc
    exact hc.aestronglyMeasurable
  have hL : Integrable L μ := by
    apply hB.mono' hLmeas
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (restrictedFieldTerminal_le_univ S hS z))]
    exact field_projection_terminal_loss_linear S hS f hf z t hε
  have hi := integral_mono hL hB (fun z => field_projection_terminal_loss_linear S hS f hf z t hε)
  change (∫ z, L z ∂μ) ≤ _
  calc
    _ ≤ ∫ z, B z ∂μ := hi
    _ = _ := by
      dsimp only [B]
      have ho := integral_add (hA.add hD)
        (integrable_const ((N : ℝ) * Real.log (1 + Real.exp (-t))) (μ := μ))
      have hi := integral_add hA hD
      change (∫ z, ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z +
        N * Real.log (1 + Real.exp (-t)) ∂μ) = _ at ho
      change (∫ z, ε * (∑ i, z i ^ 2) + (ε⁻¹ + t) * fieldProjectionDistance f z ∂μ) = _ at hi
      simp only [Pi.add_apply] at ho
      rw [ho, hi, integral_const_mul, integral_const_mul, integral_const]
      simp

end InvariantIsing

end

end OAI
