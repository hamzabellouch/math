import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CappedExcess

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma measure_positive_negative_balance (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ + (ν-μ) = ν + (μ-ν) := by
  let : IsFiniteMeasure (μ-ν) := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure (ν-μ) := isFiniteMeasure_of_le ν Measure.sub_le
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add,Measure.toSignedMeasure_add]
  have H := Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub (μ := μ) (ν := ν)
  have hh := sub_eq_sub_iff_add_eq_add.mp H
  simpa only [add_comm] using hh

lemma measure_add_left_cancel_finite (μ : Measure X) [IsFiniteMeasure μ]
    {ν ρ : Measure X} (h : μ+ν=μ+ρ) : ν=ρ :=
  le_antisymm (Measure.le_of_add_le_add_left h.le) (Measure.le_of_add_le_add_left h.ge)

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_complementarity (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ)
    (hmin : (μ-ν) univ ≤ ((μ-ρ+β)-ν) univ) :
    ((μ-ρ+β)-ν) = (μ-ν)-ρ+β ∧
      (ν-(μ-ρ+β)) = ν-μ ∧ β.MutuallySingular (ν-μ) := by
  let δ := μ-ν
  let η := μ-ρ+β
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le δ hρ
  let : IsFiniteMeasure (μ-ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure η := inferInstanceAs (IsFiniteMeasure (μ-ρ+β))
  let : IsFiniteMeasure (δ-ρ) := isFiniteMeasure_of_le δ Measure.sub_le
  let : IsFiniteMeasure (η-ν) := isFiniteMeasure_of_le η Measure.sub_le
  let : IsFiniteMeasure (ν-η) := isFiniteMeasure_of_le ν Measure.sub_le
  let : IsFiniteMeasure (ν-μ) := isFiniteMeasure_of_le ν Measure.sub_le
  have hρμ : ρ ≤ μ := hρ.trans Measure.sub_le
  have hμr : ρ+(μ-ρ) = μ := by rw [add_comm,Measure.sub_add_cancel_of_le hρμ]
  have hδr : ρ+(δ-ρ) = δ := by rw [add_comm,Measure.sub_add_cancel_of_le hρ]
  have hu : η-ν ≤ δ-ρ+β := by
    apply Measure.sub_le_of_le_add
    apply Measure.le_of_add_le_add_left (μ := ρ)
    calc
      ρ+η = μ+β := by dsimp [η]; rw [← add_assoc,hμr]
      _ ≤ (δ+ν)+β := add_le_add (measure_le_sub_add μ ν) le_rfl
      _ = (ρ+(δ-ρ)+ν)+β := congrArg (fun ζ : Measure X => (ζ+ν)+β) hδr.symm
      _ = ρ+(δ-ρ+β+ν) := by ac_rfl
  have htu : (δ-ρ+β) univ = δ univ := by
    rw [Measure.add_apply,Measure.sub_apply MeasurableSet.univ hρ,hmass]
    exact tsub_add_cancel_of_le (hρ univ)
  have hδ : η-ν = δ-ρ+β := by
    apply Measure.eq_of_le_of_measure_univ_eq hu
    apply le_antisymm (hu univ)
    rw [htu]
    exact hmin
  have hb := measure_positive_negative_balance η ν
  have hκ : ν-η = ν-μ := by
    apply measure_add_left_cancel_finite (μ+β)
    calc
      (μ+β)+(ν-η) = ρ+(η+(ν-η)) := by
        change (μ+β)+(ν-η) = ρ+((μ-ρ+β)+(ν-η))
        rw [← add_assoc ρ (μ-ρ+β) (ν-η),← add_assoc ρ (μ-ρ) β,hμr]
      _ = ρ+(ν+(η-ν)) := congrArg (fun ζ : Measure X => ρ+ζ) hb
      _ = (ρ+(δ-ρ)+ν)+β := by rw [hδ]; ac_rfl
      _ = (δ+ν)+β := by rw [hδr]
      _ = (μ+β)+(ν-μ) := by
        have HB := measure_positive_negative_balance μ ν
        change (μ-ν+ν)+β = _
        rw [add_comm (μ-ν) ν,← HB]
        ac_rfl
  refine ⟨hδ,hκ,?_⟩
  have hs : (η-ν).MutuallySingular (ν-η) := Measure.mutually_singular_measure_sub
  rw [hκ] at hs
  apply hs.mono _ le_rfl
  rw [hδ]
  exact Measure.le_add_left le_rfl

end WeakHessian
end
end InlinedFile0

end OAI
