import OAI.MeasureTheory.Falconer.Angular.CircleTests

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem source_measure_set_le_densityNorm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceDensityNorm p γ ≠ ∞)
    (S : Set UnitCircle) (hS : MeasurableSet S) :
    γ S ≤ sourceDensityNorm p γ * (sourceArcLength S)^(1-1/p) := by
  have hT : sourceTestNorm q γ ≠ ∞ := by rwa [sourceTestNorm_eq_densityNorm γ hpq]
  let f : UnitCircle → ℝ := S.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength) :=
    memLp_indicator_const _ hS _ (Or.inr (measure_ne_top _ _))
  have hb := sourceTestNorm_measurable_test_bound γ
    (Real.holderConjugate_iff.mp hpq.symm).1.le hT f hf
  have hi : ‖∫ x, f x ∂γ‖ = (γ S).toReal := by
    simp [f, integral_indicator hS, measureReal_def, Real.norm_eq_abs]
  have hn : eLpNorm f (ENNReal.ofReal q) sourceArcLength = (sourceArcLength S)^(1/q) := by
    simp only [f, eLpNorm_indicator_const hS.nullMeasurableSet (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top, enorm_one, one_mul, ENNReal.toReal_ofReal hpq.symm.nonneg]
  rw [hi, hn] at hb
  have he : (1:ℝ)/q = 1-1/p := by linarith [hpq.one_div_add_one_div]
  have ht : (sourceArcLength S)^(1/q) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hpq.symm.nonneg) (measure_ne_top _ _)
  have hb' := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hT, ENNReal.ofReal_toReal ht, he, sourceTestNorm_eq_densityNorm γ hpq] at hb'

theorem radial_cap_mass_bound (ν : Measure Plane) [IsFiniteMeasure ν] (x : Plane)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K w : ℝ≥0∞} (hK : K ≠ ∞)
    (hN : sourceDensityNorm p (ν.map (sourceRadialUnit x)) ≤ K)
    (S : Set UnitCircle) (hS : MeasurableSet S) (hSw : sourceArcLength S ≤ w) :
    ν (sourceRadialUnit x ⁻¹' S) ≤ K * w^(1-1/p) := by
  have hexp : 0 ≤ 1-1/p := by
    have he := hpq.one_div_add_one_div
    have hq := one_div_nonneg.mpr hpq.symm.nonneg
    linarith
  rw [← Measure.map_apply (measurable_sourceRadialUnit x) hS]
  exact (source_measure_set_le_densityNorm _ hpq (hN.trans_lt hK.lt_top).ne S hS).trans
    (mul_le_mul' hN (ENNReal.rpow_le_rpow hSw hexp))

end PlanarFalconer

end OAI
