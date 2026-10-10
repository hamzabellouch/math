import OAI.Probability.FreeIsing.Energy.DiscrepancyEnergy

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem martingale_integral_eq {I : Type*} [Preorder I]
    {ℱ : Filtration I mΩ} [SigmaFiniteFiltration μ ℱ]
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t) :
    (∫ ω, M t ω ∂μ) = ∫ ω, M s ω ∂μ := by
  simpa only [Measure.restrict_univ] using
    (hM.setIntegral_eq hst (s := Set.univ) MeasurableSet.univ).symm

theorem expectedSquare_ac_and_deriv_of_compensatedSquare_martingale
    [SFinite μ] {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration μ ℱ]
    {X : ℝ≥0 → Ω → ℝ} {F : ℝ → Ω → ℝ} (T : ℝ≥0)
    (hF : Integrable (fun p : ℝ × Ω => F p.1 p.2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod μ))
    (hM : Martingale
      (fun t ω => (X t ω) ^ 2 - ∫ s in (0 : ℝ)..(t : ℝ), F s ω) ℱ μ) :
    AbsolutelyContinuousOnInterval
      (fun t => ∫ ω, (X t.toNNReal ω) ^ 2 ∂μ) 0 (T : ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 (T : ℝ)),
        deriv (fun t => ∫ ω, (X t.toNNReal ω) ^ 2 ∂μ) t =
          ∫ ω, F t ω ∂μ) := by
  let N : ℝ≥0 → Ω → ℝ :=
    fun t ω => (X t ω) ^ 2 - ∫ s in (0 : ℝ)..(t : ℝ), F s ω
  have hN : Martingale N ℱ μ := hM
  have hN0 : N 0 = fun ω => (X 0 ω) ^ 2 := by
    funext ω
    simp [N]
  let M : ℝ → Ω → ℝ := fun t ω => N t.toNNReal ω - N 0 ω
  have hXa : Integrable (fun ω => (X 0 ω) ^ 2) μ := by
    simpa only [hN0] using hN.integrable 0
  have hMint (t : ℝ) : Integrable (M t) μ :=
    (hN.integrable t.toNNReal).sub (hN.integrable 0)
  have hmean (t : ℝ) : ∫ ω, M t ω ∂μ = 0 := by
    change (∫ ω, N t.toNNReal ω - N 0 ω ∂μ) = 0
    have heq : (∫ ω, N t.toNNReal ω ∂μ) = ∫ ω, N 0 ω ∂μ :=
      martingale_integral_eq hN (s := 0) (t := t.toNNReal) (by positivity)
    rw [integral_sub (hN.integrable _) (hN.integrable _), heq, sub_self]
  have hdecomp : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂μ,
      (X t.toNNReal ω) ^ 2 = (X (0 : ℝ).toNNReal ω) ^ 2 + M t ω +
        ∫ s in (0 : ℝ)..t, F s ω := by
    intro t ht
    filter_upwards with ω
    simp only [M, N, NNReal.coe_zero, Real.toNNReal_zero,
      intervalIntegral.integral_same, sub_zero, Real.coe_toNNReal t ht.1]
    ring
  have hstart : Integrable (fun ω => (X (0 : ℝ).toNNReal ω) ^ 2) μ := by
    simpa only [Real.toNNReal_zero] using hXa
  exact ⟨secondMoment_absolutelyContinuous T.2 hstart
      (fun t _ => hMint t) (fun t _ => hmean t) hF hdecomp,
    secondMoment_ae_deriv T.2 hstart
      (fun t _ => hMint t) (fun t _ => hmean t) hF hdecomp⟩

theorem secondMoment_nonneg {X : ℝ → Ω → ℝ} (t : ℝ) :
    0 ≤ ∫ ω, (X t ω) ^ 2 ∂μ :=
  integral_nonneg fun _ => sq_nonneg _

theorem secondMoment_le_of_ae_abs_le [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {t H : ℝ}
    (hInt : Integrable (fun ω => (X t ω) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ, |X t ω| ≤ H) :
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hsq : ∀ᵐ ω ∂μ, (X t ω) ^ 2 ≤ H ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).2 hω
  calc
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ ∫ _ : Ω, H ^ 2 ∂μ := integral_mono_ae hInt (integrable_const _) hsq
    _ = H ^ 2 := by simp

end Problem367.DiscrepancyEnergy

end

end OAI
