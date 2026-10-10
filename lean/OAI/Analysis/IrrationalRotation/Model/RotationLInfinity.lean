import OAI.Analysis.IrrationalRotation.Model.Rotation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.Holder

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.LInfinityRepresentative

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def value (a : Lp ℂ ∞ μ) (x : X) : ℂ :=
  if ‖(Lp.aestronglyMeasurable a).mk a x‖ ≤ ‖a‖ then
    (Lp.aestronglyMeasurable a).mk a x else 0

theorem norm_value_le (a : Lp ℂ ∞ μ) (x : X) : ‖value a x‖ ≤ ‖a‖ := by
  unfold value
  split_ifs with h
  · exact h
  · simp

theorem stronglyMeasurable_value (a : Lp ℂ ∞ μ) : StronglyMeasurable (value a) := by
  exact StronglyMeasurable.piecewise
    (measurableSet_le
      (Lp.aestronglyMeasurable a).stronglyMeasurable_mk.norm.measurable measurable_const)
    (Lp.aestronglyMeasurable a).stronglyMeasurable_mk stronglyMeasurable_const

theorem value_ae (a : Lp ℂ ∞ μ) : value a =ᵐ[μ] a := by
  have hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ ‖a‖ := by
    have h := ae_le_lpNorm_exponent_top (Lp.memLp a)
    simpa only [← toReal_eLpNorm, Lp.norm_def] using h
  filter_upwards [(Lp.aestronglyMeasurable a).ae_eq_mk, hb] with x hx hb
  simp only [value, ← hx, ite_eq_left hb]

end Invariant233.LInfinityRepresentative

namespace Invariant233.Rotation

def lInfinityProduct (a b : Lp ℂ ∞ circleMeasure) : Lp ℂ ∞ circleMeasure :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ ∞ ∞ a b

def lInfinityOrbitWeight (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) (x : Circle) :
    WeightedShift.Weight :=
  ⟨fun k => LInfinityRepresentative.value a (action θ k x), memℓp_infty <| by
    refine ⟨‖a‖, ?_⟩
    rintro r ⟨k, rfl⟩
    exact LInfinityRepresentative.norm_value_le a _⟩

def lInfinityRepresentation (θ : ℝ) (a : Lp ℂ ∞ circleMeasure) :
    Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (lInfinityOrbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun _x => lp.norm_le_of_forall_le (norm_nonneg a)
      (fun _k => LInfinityRepresentative.norm_value_le a _))
    (fun _k => ((LInfinityRepresentative.stronglyMeasurable_value a).comp_measurable
      (continuous_id.add continuous_const).measurable).aestronglyMeasurable)

end Invariant233.Rotation

end

end OAI
