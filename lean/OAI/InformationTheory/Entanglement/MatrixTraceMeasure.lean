import OAI.InformationTheory.Entanglement.DensityPositivity

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder ENNReal MeasureTheory Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter
attribute [local instance] Classical.propDecidable
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω] {n : Type} [Fintype n]
namespace PositiveMatrixMeasure
variable (W : PositiveMatrixMeasure Ω n)
def traceSigned : SignedMeasure Ω := ComplexMeasure.re (∑ i, W.entry i i)
lemma traceSigned_apply (s : Set Ω) : W.traceSigned s=(Matrix.trace (W.value s)).re := by
  change ((∑ i, W.entry i i) s).re=_
  simp only [_root_.sum_apply,value,Matrix.trace,Matrix.diag]
lemma traceSigned_nonneg : 0 ≤[Set.univ] W.traceSigned := by
  apply VectorMeasure.restrict_le_restrict_of_subset_le
  intro s hs _
  change 0≤W.traceSigned s
  rw [W.traceSigned_apply]
  exact
    (Complex.nonneg_iff.mp (W.positive s hs).trace_nonneg).1

def traceMeasure : Measure Ω :=
  W.traceSigned.toMeasureOfZeroLE Set.univ MeasurableSet.univ W.traceSigned_nonneg
instance : IsFiniteMeasure W.traceMeasure := SignedMeasure.toMeasureOfZeroLE_finite _ _ _
lemma traceMeasure_real {s : Set Ω} (hs : MeasurableSet s) :
    W.traceMeasure.real s=(Matrix.trace (W.value s)).re := by
  rw [traceMeasure,SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hs,Set.univ_inter,
    W.traceSigned_apply]
lemma trace_domination {μ : Measure Ω} (h : W.traceMeasure≪μ) :
    ∀ s, MeasurableSet s → μ s=0 → (Matrix.trace (W.value s)).re=0 := by
  intro s hs hz
  rw [← W.traceMeasure_real hs,measureReal_def,h hz,ENNReal.toReal_zero]

def positiveDensity (μ : Measure Ω) (x : Ω) : Mat n :=
  if (W.density μ x).PosSemidef then W.density μ x else 0
lemma positiveDensity_psd (μ : Measure Ω) (x : Ω) : (W.positiveDensity μ x).PosSemidef := by
  unfold positiveDensity
  split
  · assumption
  · exact Matrix.PosSemidef.zero
lemma positiveDensity_measurable [DecidableEq n] (μ : Measure Ω) :
    Measurable (W.positiveDensity μ) := by
  apply (W.density_measurable (μ := μ)).ite _ measurable_const
  simpa only [Matrix.nonneg_iff_posSemidef] using
    measurableSet_le (show Measurable (fun _ : Ω => (0 : Mat n)) from measurable_const)
      (W.density_measurable (μ := μ))
lemma positiveDensity_ae_eq {μ : Measure Ω} [SigmaFinite μ] (h : W.traceMeasure≪μ) :
    W.positiveDensity μ=ᵐ[μ] W.density μ := by
  filter_upwards [W.density_ae_psd (W.trace_domination h)] with x hx
  exact ite_eq_left hx
lemma positiveDensity_integrable {μ : Measure Ω} [SigmaFinite μ] (h : W.traceMeasure≪μ)
    (i j : n) : Integrable (fun x => W.positiveDensity μ x i j) μ := by
  refine (W.density_integrable i j).congr ?_
  filter_upwards [W.positiveDensity_ae_eq h] with x hx
  exact (congrArg (fun M : Mat n => M i j) hx).symm
lemma positiveDensity_setIntegral {μ : Measure Ω} [SigmaFinite μ] (h : W.traceMeasure≪μ)
    {s : Set Ω} (hs : MeasurableSet s) (i j : n) :
    (∫ x in s, W.positiveDensity μ x i j ∂μ)=W.value s i j := by
  rw [integral_congr_ae (ae_restrict_of_ae (W.positiveDensity_ae_eq h |>.mono
    (fun x hx => congrArg (fun M : Mat n => M i j) hx)))]
  exact W.density_setIntegral (W.trace_domination h) hs i j
lemma positiveDensity_trace_integrable {μ : Measure Ω} [SigmaFinite μ] (h : W.traceMeasure≪μ) :
    Integrable (fun x => (Matrix.trace (W.positiveDensity μ x)).re) μ := by
  exact (integrable_finsetSum _ fun i _ => W.positiveDensity_integrable h i i).re
lemma positiveDensity_trace_setIntegral {μ : Measure Ω} [SigmaFinite μ] (h : W.traceMeasure≪μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, (Matrix.trace (W.positiveDensity μ x)).re ∂μ)=W.traceMeasure.real s := by
  rw [W.traceMeasure_real hs]
  change (∫ x in s, RCLike.re (Matrix.trace (W.positiveDensity μ x)) ∂μ)=_
  have hi : Integrable (fun x => Matrix.trace (W.positiveDensity μ x)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => W.positiveDensity_integrable h i i)
  rw [integral_re hi.integrableOn]
  exact congrArg Complex.re ((integral_finsetSum Finset.univ
    (fun i _ => (W.positiveDensity_integrable h i i).integrableOn)).trans
    (Finset.sum_congr rfl (fun i _ => W.positiveDensity_setIntegral h hs i i)))
end PositiveMatrixMeasure

end SecretKey

end

end OAI
