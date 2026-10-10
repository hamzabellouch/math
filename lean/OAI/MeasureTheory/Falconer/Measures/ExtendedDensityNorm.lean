import OAI.MeasureTheory.Falconer.Radial.RadonLpDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceDensityNorm (p : ℝ) (γ : Measure UnitCircle) : ℝ≥0∞ := by
  classical
  exact if γ ≪ sourceArcLength then
    eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength
  else ∞

theorem sourceTestNorm_le_rnDeriv_norm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hAC : γ ≪ sourceArcLength) :
    sourceTestNorm q γ ≤
      eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength := by
  let R := γ.rnDeriv sourceArcLength
  have hm : Measurable R := Measure.measurable_rnDeriv _ _
  have hn : eLpNorm (fun x => (R x).toReal) (ENNReal.ofReal p) sourceArcLength =
      (∫⁻ x, R x^p ∂sourceArcLength)^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top hm.ennreal_toReal.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top γ sourceArcLength] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx.ne]
  rw [hn]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have hG : Measurable (fun x => ‖F x‖ₑ) := F.continuous.enorm.measurable
  have hq : (∫⁻ x, ‖F x‖ₑ^q ∂sourceArcLength)^(1/q) ≤ 1 := by
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top F.continuous.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.symm.nonneg] at hF
  have hb := enorm_integral_le_lintegral_enorm (μ := γ) (fun x => F x)
  rw [← ofReal_norm] at hb
  have he : (∫⁻ x, ‖F x‖ₑ ∂γ) = ∫⁻ x, R x * ‖F x‖ₑ ∂sourceArcLength := by
    have h := lintegral_withDensity_eq_lintegral_mul sourceArcLength hm hG
    rw [Measure.withDensity_rnDeriv_eq γ sourceArcLength hAC] at h
    exact h
  rw [he] at hb
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq sourceArcLength hpq hm.aemeasurable hG.aemeasurable
  exact hb.trans (hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _)))

theorem sourceTestNorm_eq_densityNorm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    sourceTestNorm q γ = sourceDensityNorm p γ := by
  unfold sourceDensityNorm
  split_ifs with hAC
  · apply le_antisymm (sourceTestNorm_le_rnDeriv_norm γ hpq hAC)
    by_cases hN : sourceTestNorm q γ = ∞
    · rw [hN]; exact le_top
    · exact sourceTestNorm_rnDeriv_eLpNorm_le γ hpq hN
  · by_contra h
    exact hAC (sourceTestNorm_absolutelyContinuous γ
      (Real.holderConjugate_iff.mp hpq.symm).1.le h)

theorem sourceDensityNorm_exists_density (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceDensityNorm p γ ≠ ∞) :
    ∃ g : UnitCircle → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      MemLp g (ENNReal.ofReal p) sourceArcLength ∧
      sourceArcLength.withDensity (fun x => ENNReal.ofReal (g x)) = γ ∧
      eLpNorm g (ENNReal.ofReal p) sourceArcLength = sourceDensityNorm p γ := by
  have hT : sourceTestNorm q γ ≠ ∞ := by rwa [sourceTestNorm_eq_densityNorm γ hpq]
  have hAC := sourceTestNorm_absolutelyContinuous γ (Real.holderConjugate_iff.mp hpq.symm).1.le hT
  let g := fun x => (γ.rnDeriv sourceArcLength x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv γ sourceArcLength).ennreal_toReal
  have hn : eLpNorm g (ENNReal.ofReal p) sourceArcLength = sourceDensityNorm p γ := by
    simp only [sourceDensityNorm, ite_eq_left hAC, g]
  refine ⟨g, hg, fun _ => ENNReal.toReal_nonneg, ?_, ?_, hn⟩
  · exact hn.trans_lt hN.lt_top
  · have he : (fun x => ENNReal.ofReal (g x)) =ᵐ[sourceArcLength] γ.rnDeriv sourceArcLength := by
      filter_upwards [Measure.rnDeriv_lt_top γ sourceArcLength] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae he]
    exact Measure.withDensity_rnDeriv_eq γ sourceArcLength hAC

end PlanarFalconer

end OAI
