import OAI.MeasureTheory.Falconer.Measures.TestNormMeasurable
import OAI.MeasureTheory.Falconer.Measures.BoundedDualDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_bounded_density_lower (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceTestNorm q γ ≠ ∞)
    (F : UnitCircle → ℝ≥0∞) (hF : Measurable F) {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hFR : ∀ᵐ x ∂sourceArcLength, F x ≤ γ.rnDeriv sourceArcLength x) :
    (∫⁻ x, F x^p ∂sourceArcLength)^(1/p) ≤ sourceTestNorm q γ := by
  have hq : 1 ≤ q := (Real.holderConjugate_iff.mp hpq.symm).1.le
  have hAC := sourceTestNorm_absolutelyContinuous γ hq hN
  have hmass : (∫⁻ x, F x^p ∂sourceArcLength) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ x, F x^p ∂sourceArcLength) ≤ ∫⁻ _, B^p ∂sourceArcLength :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hFB x) hpq.nonneg)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg hB).lt_top
          (measure_lt_top sourceArcLength univ)
  by_cases hzero : (∫⁻ x, F x^p ∂sourceArcLength) = 0
  · rw [hzero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos)]
    exact bot_le
  obtain ⟨h, hh, ⟨C, hC, hhC⟩, hnorm, hpair⟩ :=
    exists_bounded_normalized_dual_density sourceArcLength F hF hpq hB hFB hzero hmass
  have hht (x : UnitCircle) : h x ≠ ∞ := ne_of_lt ((hhC x).trans_lt hC.lt_top)
  have hen (x : UnitCircle) : ‖(h x).toReal‖ₑ = h x := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hht x)]
  have hm : MemLp (fun x => (h x).toReal) (ENNReal.ofReal q) (γ + sourceArcLength) :=
    (memLp_top_of_bound hh.ennreal_toReal.aestronglyMeasurable C.toReal
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono hC (hhC x)))).mono_exponent le_top
  have hn : eLpNorm (fun x => (h x).toReal) (ENNReal.ofReal q) sourceArcLength = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top hh.ennreal_toReal.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp_rw [hen]
    rw [hnorm, ENNReal.one_rpow]
  have hb := sourceTestNorm_measurable_test_bound γ hq hN (fun x => (h x).toReal) hm
  rw [hn, ENNReal.toReal_one, mul_one] at hb
  have hi : Integrable (fun x => (h x).toReal) γ :=
    (hm.mono_measure (le_add_of_nonneg_right bot_le)).integrable
      (by simpa using ENNReal.ofReal_le_ofReal hq)
  have hlin : (∫⁻ x, h x ∂γ) ≤ sourceTestNorm q γ := by
    have he : ENNReal.ofReal ‖∫ x, (h x).toReal ∂γ‖ = ∫⁻ x, h x ∂γ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => ENNReal.toReal_nonneg)),
        ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
      exact lintegral_congr (fun x => ENNReal.ofReal_toReal (hht x))
    rw [← he]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mpr hb
  rw [← hpair]
  calc
    (∫⁻ x, F x * h x ∂sourceArcLength) ≤
        ∫⁻ x, γ.rnDeriv sourceArcLength x * h x ∂sourceArcLength :=
      lintegral_mono_ae (hFR.mono (fun x hx => mul_le_mul_left hx _))
    _ = ∫⁻ x, h x ∂γ := by
      have he := lintegral_withDensity_eq_lintegral_mul sourceArcLength
        (Measure.measurable_rnDeriv γ sourceArcLength) hh
      rw [Measure.withDensity_rnDeriv_eq γ sourceArcLength hAC] at he
      exact he.symm
    _ ≤ _ := hlin

end PlanarFalconer

end OAI
