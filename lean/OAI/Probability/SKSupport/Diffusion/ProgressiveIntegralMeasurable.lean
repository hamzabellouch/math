import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_integral_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive ℱ α) (s : ℝ≥0) {w : ℝ → ℝ}
    (hw : Measurable w) :
    Measurable[ℱ s] (fun ω => ∫ r in (0:ℝ)..(s:ℝ), w r*α (Real.toNNReal r) ω) := by
  let clip (p : ℝ × Ω) := α (min (Real.toNNReal p.1) s) p.2
  have htime : Measurable[(borel ℝ).prod (ℱ s)]
      (fun p : ℝ × Ω => min (Real.toNNReal p.1) s) :=
    (measurable_fst.real_toNNReal).min measurable_const
  have hclip : Measurable[(borel ℝ).prod (ℱ s)] clip := by
    exact (hα s).comp ((htime.subtype_mk (h := fun p : ℝ × Ω => (min_le_right (Real.toNNReal p.1) s))).prodMk measurable_snd)
  have hwm : Measurable[(borel ℝ).prod (ℱ s)] (fun p : ℝ × Ω => w p.1*clip p) :=
    (hw.comp measurable_fst).mul hclip
  have hint : Measurable[ℱ s]
      (fun ω => ∫ r in (0:ℝ)..(s:ℝ), w r*clip (r,ω)) := by
    let : MeasurableSpace Ω := ℱ s
    simp_rw [intervalIntegral.integral_of_le s.coe_nonneg]
    exact hwm.stronglyMeasurable.integral_prod_left.measurable
  convert hint using 1
  funext ω
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le s.coe_nonneg] at hr
  have hle : Real.toNNReal r ≤ s := by
    exact Real.toNNReal_le_iff_le_coe.mpr hr.2
  simp only [clip, min_eq_left hle]

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
