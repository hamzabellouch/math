import OAI.InformationTheory.Entanglement.MatrixTraceMeasure

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder ENNReal MeasureTheory Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter
attribute [local instance] Classical.propDecidable
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω] {n : Type} [Fintype n]
variable {ι : Type*} [Fintype ι]

def familyTraceMeasure (W : ι → PositiveMatrixMeasure Ω n) : Measure Ω :=
  ∑ a, (W a).traceMeasure
instance familyTraceMeasureIsFiniteMeasure (W : ι → PositiveMatrixMeasure Ω n) :
    IsFiniteMeasure (familyTraceMeasure W) := by
  unfold familyTraceMeasure
  infer_instance
lemma trace_absolutelyContinuous_family (W : ι → PositiveMatrixMeasure Ω n) (a : ι) :
    (W a).traceMeasure ≪ familyTraceMeasure W := by
  apply Measure.absolutelyContinuous_of_le
  exact Finset.single_le_sum (f := fun i => (W i).traceMeasure)
    (fun i _ => by exact bot_le) (Finset.mem_univ a)
lemma familyTraceMeasure_real (W : ι → PositiveMatrixMeasure Ω n) (s : Set Ω) :
    (familyTraceMeasure W).real s=∑ a, (W a).traceMeasure.real s := by
  simp only [familyTraceMeasure,measureReal_def,Measure.coe_finsetSum,Finset.sum_apply]
  exact ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)

def familyDensity (W : ι → PositiveMatrixMeasure Ω n) (a : ι) : Ω → Mat n :=
  (W a).positiveDensity (familyTraceMeasure W)
lemma familyDensity_psd (W : ι → PositiveMatrixMeasure Ω n) (a : ι) (t : Ω) :
    (familyDensity W a t).PosSemidef := (W a).positiveDensity_psd _ _
lemma familyDensity_measurable [DecidableEq n] (W : ι → PositiveMatrixMeasure Ω n) (a : ι) :
    Measurable (familyDensity W a) := (W a).positiveDensity_measurable _
lemma familyDensity_integrable (W : ι → PositiveMatrixMeasure Ω n) (a : ι) (i j : n) :
    Integrable (fun t => familyDensity W a t i j) (familyTraceMeasure W) :=
  (W a).positiveDensity_integrable (trace_absolutelyContinuous_family W a) i j
lemma familyDensity_trace_integrable (W : ι → PositiveMatrixMeasure Ω n) (a : ι) :
    Integrable (fun t => (Matrix.trace (familyDensity W a t)).re) (familyTraceMeasure W) :=
  (W a).positiveDensity_trace_integrable (trace_absolutelyContinuous_family W a)
lemma familyDensity_setIntegral (W : ι → PositiveMatrixMeasure Ω n) (a : ι)
    {s : Set Ω} (hs : MeasurableSet s) (i j : n) :
    (∫ t in s, familyDensity W a t i j ∂familyTraceMeasure W)=(W a).value s i j :=
  (W a).positiveDensity_setIntegral (trace_absolutelyContinuous_family W a) hs i j
lemma familyDensity_trace_setIntegral (W : ι → PositiveMatrixMeasure Ω n) (a : ι)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ t in s, (Matrix.trace (familyDensity W a t)).re ∂familyTraceMeasure W)=
      (W a).traceMeasure.real s :=
  (W a).positiveDensity_trace_setIntegral (trace_absolutelyContinuous_family W a) hs

theorem familyDensity_trace_sum_one (W : ι → PositiveMatrixMeasure Ω n) :
    ∀ᵐ t ∂familyTraceMeasure W, (∑ a, (Matrix.trace (familyDensity W a t)).re)=1 := by
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (integrable_finsetSum _ (fun a _ => familyDensity_trace_integrable W a))
    (integrable_const (1 : ℝ)) ?_
  intro s hs _
  rw [integral_finsetSum _ (fun a _ => (familyDensity_trace_integrable W a).integrableOn)]
  simp_rw [familyDensity_trace_setIntegral W _ hs]
  rw [← familyTraceMeasure_real]
  simp
lemma familyDensity_total_integral (W : ι → PositiveMatrixMeasure Ω n) :
    (∑ a, ∫ t, (Matrix.trace (familyDensity W a t)).re ∂familyTraceMeasure W)=
      (familyTraceMeasure W).real Set.univ := by
  rw [familyTraceMeasure_real]
  apply Finset.sum_congr rfl
  intro a _
  simpa using familyDensity_trace_setIntegral W a MeasurableSet.univ

end SecretKey

end

end OAI
