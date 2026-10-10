import OAI.Analysis.Pureness.Quasitrace.QuasitraceCauchy

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
include hadd

lemma isMetricCauchy_realPart {u : ℕ → D} (hu : T.IsMetricCauchy u) :
    T.IsMetricCauchy (fun k => (ℜ (u k) : D)) := by
  have h := T.isMetricCauchy_smul (T.isMetricCauchy_add hadd hu (T.isMetricCauchy_star hu))
    ((2 : ℝ)⁻¹ : ℂ)
  simpa only [realPart_apply_coe,← Complex.ofReal_inv,Complex.coe_smul] using h
lemma isMetricCauchy_imaginaryPart {u : ℕ → D} (hu : T.IsMetricCauchy u) :
    T.IsMetricCauchy (fun k => (ℑ (u k) : D)) := by
  have h := T.isMetricCauchy_smul
    (T.isMetricCauchy_smul (T.isMetricCauchy_add hadd hu (T.isMetricCauchy_neg (T.isMetricCauchy_star hu)))
      ((2 : ℝ)⁻¹ : ℂ)) (-Complex.I)
  simpa only [imaginaryPart_apply_coe,← Complex.ofReal_inv,Complex.coe_smul,sub_eq_add_neg] using h
lemma isMetricNull_realPart {u : ℕ → D} (hu : T.IsMetricNull u) :
    T.IsMetricNull (fun k => (ℜ (u k) : D)) := by
  have h := T.isMetricNull_smul (T.isMetricNull_add hadd hu (T.isMetricNull_star hu))
    ((2 : ℝ)⁻¹ : ℂ)
  simpa only [realPart_apply_coe,← Complex.ofReal_inv,Complex.coe_smul] using h
lemma isMetricNull_imaginaryPart {u : ℕ → D} (hu : T.IsMetricNull u) :
    T.IsMetricNull (fun k => (ℑ (u k) : D)) := by
  have h := T.isMetricNull_smul
    (T.isMetricNull_smul (T.isMetricNull_add hadd hu (T.isMetricNull_neg (T.isMetricNull_star hu)))
      ((2 : ℝ)⁻¹ : ℂ)) (-Complex.I)
  simpa only [imaginaryPart_apply_coe,← Complex.ofReal_inv,Complex.coe_smul,sub_eq_add_neg] using h
end CuntzPureness.PositiveQuasitrace

end

end OAI
