import OAI.InformationTheory.Entanglement.InstrumentCovariance
import OAI.InformationTheory.Entanglement.ProbeFactorization

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : Type} [Fintype n] [DecidableEq n]
namespace PositiveMatrixMeasure

def testMeasure (W : PositiveMatrixMeasure Ω n) (E : Mat n) : Measure Ω :=
  (W.filter (CFC.sqrt E)).traceMeasure
instance (W : PositiveMatrixMeasure Ω n) (E : Mat n) : IsFiniteMeasure (W.testMeasure E) := by
  unfold testMeasure
  infer_instance
lemma testMeasure_real (W : PositiveMatrixMeasure Ω n) {E : Mat n} (hE : E.PosSemidef)
    {s : Set Ω} (hs : MeasurableSet s) :
    (W.testMeasure E).real s=(Matrix.trace (E*W.value s)).re := by
  rw [testMeasure,traceMeasure_real _ hs,filter_value,trace_filter hE]
lemma testMeasure_density (W : PositiveMatrixMeasure Ω n) {E : Mat n} (hE : E.PosSemidef)
    {μ : Measure Ω} [IsFiniteMeasure μ] (hW : W.traceMeasure≪μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ t in s, (Matrix.trace (E*W.positiveDensity μ t)).re ∂μ)=(W.testMeasure E).real s := by
  rw [testMeasure_real W hE hs]
  change (∫ t in s, RCLike.re (Matrix.trace (E*W.positiveDensity μ t)) ∂μ)=_
  have hi : Integrable (fun t => Matrix.trace (E*W.positiveDensity μ t)) (μ.restrict s) := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((W.positiveDensity_integrable hW j i).integrableOn).const_mul _
  rw [integral_re hi]
  change Complex.re (∫ t in s, Matrix.trace (E*W.positiveDensity μ t) ∂μ)=_
  apply congrArg Complex.re
  change (∫ t in s, ∑ i : n, ∑ j : n, E i j*W.positiveDensity μ t j i ∂μ)=
    ∑ i : n, ∑ j : n, E i j*W.value s j i
  rw [integral_finsetSum (Finset.univ : Finset n) (fun i _ => integrable_finsetSum (Finset.univ : Finset n) (fun j _ =>
    ((W.positiveDensity_integrable hW j i).integrableOn).const_mul (E i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum (Finset.univ : Finset n) (fun j _ => ((W.positiveDensity_integrable hW j i).integrableOn).const_mul (E i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,W.positiveDensity_setIntegral hW hs]
end PositiveMatrixMeasure
namespace CPOutcomeLaw
variable (L : CPOutcomeLaw Ω n)

lemma probe_test_value (E : Mat n) (s : Set Ω) :
    Matrix.trace (E*L.probe.value s)=L.law Eᵀ s := by
  rw [L.law_expand]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,probe_value]
  rw [Finset.sum_comm]
lemma probe_testMeasure_real {E : Mat n} (hE : E.PosSemidef) {s : Set Ω} (hs : MeasurableSet s) :
    (L.probe.testMeasure E).real s=(L.law Eᵀ s).re := by
  rw [PositiveMatrixMeasure.testMeasure_real _ hE hs,L.probe_test_value]

end CPOutcomeLaw
end SecretKey

end

end OAI
