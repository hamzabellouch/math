import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL2
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! A quantitative change of variables for the short Lipschitz sampling maps.
The product plane uses its original sup norm and product Lebesgue measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem planar_map_le_four (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) :
    Measure.map phi planeMeasure≤(4:ℝ≥0∞) • planeMeasure := by
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply hm hS,Measure.smul_apply,smul_eq_mul]
  have h := ha.hausdorffMeasure_preimage_le (d:=2) (by norm_num) S
  norm_num only [hausdorffMeasure_prod_real,Measure.volume_eq_prod,ENNReal.rpow_two,
    ENNReal.coe_ofNat,show (2:ℝ≥0∞)^2=4 by norm_num] at h
  exact h

theorem planar_integral_comp_le_four (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (g : (ℝ×ℝ) → ℝ) (hg : Integrable g planeMeasure)
    (hgn : ∀ z, 0≤g z) :
    Integrable (g ∘ phi) planeMeasure ∧
      (∫ z, g (phi z) ∂planeMeasure)≤4*∫ z, g z ∂planeMeasure := by
  have hmap := planar_map_le_four phi hm ha
  have hi : Integrable g (Measure.map phi planeMeasure) :=
    (hg.smul_measure (by norm_num : (4:ℝ≥0∞)≠⊤)).mono_measure hmap
  refine ⟨hi.comp_measurable hm,?_⟩
  rw [←integral_map hm.aemeasurable hi.aestronglyMeasurable]
  have h := integral_mono_measure hmap (Filter.Eventually.of_forall hgn)
    (hg.smul_measure (by norm_num : (4:ℝ≥0∞)≠⊤))
  simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using h

theorem planar_memLp_comp_bound (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (f ∘ phi) 2 planeMeasure ∧
      (∫ z, ‖f (phi z)‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_comp_le_four phi hm ha (fun z => ‖f z‖^2)
    (hf.integrable_norm_pow (by decide : 2≠0)) (fun z => sq_nonneg _)
  exact ⟨(memLp_two_iff_integrable_sq_norm (hfm.comp hm).aestronglyMeasurable).2 h.1,h.2⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
