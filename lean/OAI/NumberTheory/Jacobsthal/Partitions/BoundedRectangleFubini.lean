import OAI.NumberTheory.Jacobsthal.Estimates.LossBounds
import OAI.NumberTheory.Jacobsthal.Estimates.ScalarFreeGate

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosOmissionBindings

theorem bounded_rectangle_integrable {f : ℝ×ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b,∀ y ∈ Icc c d,|f (x,y)| ≤ C) :
    Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc c d)
  let : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmem : ∀ᵐ p : ℝ×ℝ ∂μ.prod ν,p.1 ∈ Icc a b ∧ p.2 ∈ Icc c d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact ⟨hx,hy⟩
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hmem] with p hp
  simpa only [Real.norm_eq_abs] using hbound p.1 hp.1 p.2 hp.2

theorem bounded_rectangle_swap {f : ℝ×ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b,∀ y ∈ Icc c d,|f (x,y)| ≤ C) :
    (∫ x in Icc a b,∫ y in Icc c d,f (x,y))=
      ∫ y in Icc c d,∫ x in Icc a b,f (x,y) := by
  exact integral_integral_swap (bounded_rectangle_integrable hf a b c d C hbound)

end ErdosOmissionBindings

end

end Erdos970

end OAI
