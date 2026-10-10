import OAI.MeasureTheory.Falconer.Estimates.FarRegionSplit
import OAI.MeasureTheory.Falconer.Estimates.KernelL1Comparison

namespace OAI

/-! # Summing the actual far regions with a uniform replacement error -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem far_integral_assembly (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (f g : ((Space d × Space d) × (Space d × Space d)) → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnc : ∀ z ∈ leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h, ‖f z‖ ≤ ε)
    (herr : ∀ z ∈ comparableFarRegion d a h, ‖f z-g z‖ ≤ ε) :
    (∫⁻ z in farDisplacementRegion d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      (∑ b ∈ Finset.Icc (a+9) (h+6),
        ∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
          ENNReal.ofReal ‖g z‖ ∂μ) +
      (2+((Finset.Icc (a+9) (h+6)).card:ℝ≥0∞))*ENNReal.ofReal ε*μ univ := by
  have hl : (∫⁻ z in leftNoncomparableFar d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_restrict_le_of_bound μ (leftNoncomparableFar_measurable d a h)
      f (fun z hz => hnc z (Or.inl hz))).trans
      (mul_le_mul' le_rfl (measure_mono (subset_univ _)))
  have hr : (∫⁻ z in rightNoncomparableFar d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_restrict_le_of_bound μ (rightNoncomparableFar_measurable d a h)
      f (fun z hz => hnc z (Or.inr hz))).trans
      (mul_le_mul' le_rfl (measure_mono (subset_univ _)))
  have hb (b : ℕ) :
      (∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
        ENNReal.ofReal ‖f z‖ ∂μ) ≤
      (∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
        ENNReal.ofReal ‖g z‖ ∂μ) + ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_replacement μ
      ((comparableFarRegion_measurable d a h).inter (comparableLengthBand_measurable d b))
      f g hε (fun z hz => herr z hz.1)).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl (measure_mono (subset_univ _))))
  apply (lintegral_far_split_bands d a h μ (fun z => ENNReal.ofReal ‖f z‖)).trans
  calc
    _ ≤ ENNReal.ofReal ε*μ univ+ENNReal.ofReal ε*μ univ+
        ∑ b ∈ Finset.Icc (a+9) (h+6),
          ((∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
            ENNReal.ofReal ‖g z‖ ∂μ)+ENNReal.ofReal ε*μ univ) :=
      add_le_add (add_le_add hl hr) (Finset.sum_le_sum (fun b _ => hb b))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring

end Falconer

end OAI
