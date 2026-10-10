import OAI.Analysis.CircleDomains.Sobolev.L2PositiveTests
import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic

namespace OAI

/-! A finite-energy extended density has a Borel real L² representative.
Its infinite values are retained separately as a reference-null Borel set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma lintegral_ofReal_toReal_eq_away_infinity
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (h : Z → ℝ≥0∞)
    (hnull : μ {z | h z = ∞} = 0) :
    (∫⁻ z, ENNReal.ofReal ((h z).toReal) ∂μ) = ∫⁻ z, h z ∂μ := by
  apply lintegral_congr_ae
  have he : ∀ᵐ z ∂μ, h z ≠ ∞ := by
    simpa only [ae_iff,not_not] using hnull
  exact he.mono (fun z hz => ENNReal.ofReal_toReal hz)

lemma extended_density_L2
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (h : Z → ℝ≥0∞) (hh : Measurable h) {D : ℝ} (hD : 0 ≤ D)
    (henergy : (∫⁻ z, h z^2 ∂σ) ≤ ENNReal.ofReal D) :
    Measurable (fun z => (h z).toReal) ∧
      ∃ hu : MemLp (fun z => (h z).toReal) 2 σ,
        ‖hu.toLp (fun z => (h z).toReal)‖^2 ≤ D ∧
        MeasurableSet {z | h z = ∞} ∧ σ {z | h z = ∞} = 0 := by
  have hm := hh.ennreal_toReal
  have hfinite : ∀ᵐ z ∂σ, h z ≠ ∞ := by
    have hs := ae_lt_top (hh.pow_const 2) (henergy.trans_lt ENNReal.ofReal_lt_top).ne
    filter_upwards [hs] with z hz
    intro ht
    simp only [ht,ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0),lt_self_iff_false] at hz
  have hE : (∫⁻ z, ENNReal.ofReal ((h z).toReal^2) ∂σ) ≤ ENNReal.ofReal D := by
    refine (lintegral_mono (fun z => ?_)).trans henergy
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  have hi : Integrable (fun z => (h z).toReal^2) σ :=
    ⟨(hm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z => sq_nonneg ((h z).toReal)))).mpr
        (hE.trans_lt ENNReal.ofReal_lt_top)⟩
  let hu : MemLp (fun z => (h z).toReal) 2 σ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  refine ⟨hm,hu,?_,hh (measurableSet_singleton ∞),?_⟩
  · have heq : (∫ z, (h z).toReal^2 ∂σ) = ‖hu.toLp (fun z => (h z).toReal)‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with z hz
      simp only [hz,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun z => sq_nonneg ((h z).toReal))),heq] at hE
    exact (ENNReal.ofReal_le_ofReal_iff hD).mp hE
  · simpa only [ae_iff,not_not] using hfinite

end CircleDomainRigidity

end

end OAI
