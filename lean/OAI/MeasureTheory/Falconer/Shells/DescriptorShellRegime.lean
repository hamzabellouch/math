import OAI.MeasureTheory.Falconer.Estimates.DescriptorInverseRegime
import OAI.MeasureTheory.Falconer.Radial.RadialShellMeasure

namespace OAI

/-! # The actual source shell satisfies the descriptor stationary regime -/

namespace Falconer
open Set MeasureTheory

theorem source_shell_frequency_bounds (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      (2:ℝ)^v/4 < r ∧ r < 4*(2:ℝ)^v := by
  have hn : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      Ψ (r/(2:ℝ)^v) ≠ 0 := by
    unfold PlanarFalconer.sourceAngularShellMeasure
    apply (ae_withDensity_iff (by fun_prop)).mpr
    filter_upwards with r hr
    intro hz
    apply hr
    simp only [hz,zero_div,ENNReal.ofReal_zero]
  filter_upwards [hn] with r hr
  have h := hsupp _ hr
  constructor
  · have hl := (lt_div_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.1
    linarith
  · exact (div_lt_iff₀ (show 0 < (2:ℝ)^v by positivity)).mp h.2

theorem eventual_descriptor_source_shell_regime {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        1 ≤ r*(2:ℝ)^(-a) ∧
        (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
        r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a) ∧
        (descriptorDerivativeScale N σ L)^2/(r*(2:ℝ)^(-a)) ≤ ((2:ℝ)^N)^(-17*σ) := by
  obtain ⟨N₀,hN₀⟩ := eventual_descriptor_inverse_frequency hσ hσ1
  refine ⟨N₀,?_⟩
  intro N hN L a v hLN hq hL
  filter_upwards [source_shell_frequency_bounds v Ψ hΨ hsupp] with r hr
  obtain ⟨hD,hDu,hΛ,hR⟩ := hN₀ N hN L (v-a) (r*(2:ℝ)^(-a)) hLN hq hL
    (dyadic_shell_frequency_lower hr.1.le)
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  have hsmall : ((2:ℝ)^N)^(-17*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  refine ⟨hD,hDu,hΛ,(div_le_one hΛpos).mp (hR.trans hsmall),?_,hR⟩
  calc
    _ ≤ (4*(2:ℝ)^v)*(2:ℝ)^(-a) :=
      mul_le_mul_of_nonneg_right hr.2.le (by positivity)
    _ = 4*(2:ℝ)^(v-a) := by
      rw [mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 2

theorem eventually_separated_inverse_frequency {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D r s t : ℝ, 1 ≤ D → 0 < s → δ ≤ t/s →
      0 < r*s → D^2/(r*s) ≤ ((2:ℝ)^N)^(-17*σ) →
      1 ≤ r*t ∧ D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hσ δ⁻¹
  refine ⟨N₀,?_⟩
  intro N hN D r s t hD hs ht hΛ hratio
  have hr : 0 < r := (mul_pos_iff_of_pos_right hs).mp hΛ
  have hst : δ*s ≤ t := (le_div_iff₀ hs).mp ht
  have hδΛ : 0 < (r*s)*δ := mul_pos hΛ hδ
  have hlower : (r*s)*δ ≤ r*t := by nlinarith [mul_le_mul_of_nonneg_left hst hr.le]
  have hrt : 0 < r*t := hδΛ.trans_le hlower
  have hbound : D^2/(r*t) ≤ ((2:ℝ)^N)^(-16*σ) := by
    calc
      _ ≤ D^2/((r*s)*δ) := div_le_div_of_nonneg_left (sq_nonneg _) hδΛ hlower
      _ = δ⁻¹*(D^2/(r*s)) := by ring
      _ ≤ δ⁻¹*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hδ.le)
      _ ≤ ((2:ℝ)^N)^σ*((2:ℝ)^N)^(-17*σ) :=
        mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
      _ = ((2:ℝ)^N)^(-16*σ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
  have hsmall : ((2:ℝ)^N)^(-16*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  exact ⟨(one_le_pow₀ hD).trans ((div_le_one hrt).mp (hbound.trans hsmall)),hbound⟩


theorem eventual_descriptor_pair_shell_regime {d : ℕ} {σ δ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a v : ℝ), L ≤ N →
      20*σ*(N:ℝ) ≤ v-a → (L:ℝ) ≤ (v-a)/2+σ*(N:ℝ) →
      ∀ (μ ν : Measure (Space d)),
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/(2:ℝ)^(-a)) →
      ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        1 ≤ descriptorDerivativeScale N σ L ∧
        descriptorDerivativeScale N σ L ≤ ((2:ℝ)^N)^2 ∧
        (0 < r*(2:ℝ)^(-a) ∧
          (descriptorDerivativeScale N σ L)^2 ≤ r*(2:ℝ)^(-a) ∧
          r*(2:ℝ)^(-a) ≤ 4*(2:ℝ)^(v-a)) ∧
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧
          (descriptorDerivativeScale N σ L)^2/(r*dist z.1 z.2) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₁,hN₁⟩ := eventual_descriptor_source_shell_regime hσ hσ1 Ψ hΨ hsupp
  obtain ⟨N₂,hN₂⟩ := eventually_separated_inverse_frequency hσ hδ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN L a v hLN hq hL μ ν hsep
  filter_upwards [hN₁ N ((le_max_left _ _).trans hN) L a v hLN hq hL] with r hr
  obtain ⟨hD,hDu,hΛ,hDΛ,hΛu,hratio⟩ := hr
  have hΛpos : 0 < r*(2:ℝ)^(-a) := zero_lt_one.trans_le hΛ
  refine ⟨hD,hDu,⟨hΛpos,hDΛ,hΛu⟩,?_⟩
  filter_upwards [hsep] with z hz
  exact hN₂ N ((le_max_right _ _).trans hN) _ r ((2:ℝ)^(-a)) (dist z.1 z.2)
    hD (by positivity) hz hΛpos hratio

end Falconer

end OAI
