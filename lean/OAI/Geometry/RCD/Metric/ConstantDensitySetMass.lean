import OAI.Geometry.RCD.Metric.ConstantDensityMeasure

namespace OAI

/-! # Exact masses of interior sets for a constant-density measure -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem real_eq_mul_volume_of_restrict_eq {n : ℕ} (μ : Measure (Euclidean n))
    {U A : Set (Euclidean n)} {c : ℝ} (hc : 0 ≤ c)
    (he : μ.restrict U = ENNReal.ofReal c • volume.restrict U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) : μ.real A=c*volume.real A := by
  have hh := congrArg (fun ν : Measure (Euclidean n) => ν A) he
  simp only [Measure.restrict_apply hA,inter_eq_left.mpr hAU,Measure.smul_apply,
    smul_eq_mul] at hh
  rw [Measure.real,hh,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc]
  rfl

end RegularPointCoordinates

end

end OAI
