import OAI.InformationTheory.Entanglement.HilbertENorm
import OAI.InformationTheory.Entanglement.MatrixMeasureChannel

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder ENNReal MeasureTheory
open ContinuousLinearMap Matrix MeasureTheory
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

structure PositiveHilbertMeasure (T H : Type*) [MeasurableSpace T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) where
  value : Set T → H →L[ℂ] H
  coeff : H → H → ComplexMeasure T
  coeff_value : ∀ x y s, MeasurableSet s → coeff x y s=inner ℂ x (value s y)
  positive : ∀ s, MeasurableSet s → HasFinitePositiveTrace b (value s)
  traceMeasure : Measure T
  traceFinite : IsFiniteMeasure traceMeasure
  trace_value : ∀ s, MeasurableSet s → traceMeasure.real s=hilbertTrace b (value s)
attribute [instance] PositiveHilbertMeasure.traceFinite
namespace PositiveHilbertMeasure
variable {b : HilbertBasis ι ℂ H} (W : PositiveHilbertMeasure T H b)
def compress (v : n → H) : PositiveMatrixMeasure T n where
  entry i j := W.coeff (v i) (v j)
  positive s hs := by
    have he : (fun i j => W.coeff (v i) (v j) s)=hilbertCompress v (W.value s) := by
      ext i j; exact W.coeff_value _ _ _ hs
    rw [he]
    exact hilbertCompress_psd v (W.positive s hs).1
omit [DecidableEq n] in
lemma compress_value (v : n → H) {s : Set T} (hs : MeasurableSet s) :
    (W.compress v).value s=hilbertCompress v (W.value s) := by
  ext i j; exact W.coeff_value _ _ _ hs

def traceComplex : ComplexMeasure T := W.traceMeasure.toSignedMeasure.toComplexMeasure 0
lemma traceComplex_value {s : Set T} (hs : MeasurableSet s) :
    W.traceComplex s=(hilbertTrace b (W.value s) : ℂ) := by
  unfold traceComplex
  rw [SignedMeasure.toComplexMeasure_apply,Measure.toSignedMeasure_apply_measurable hs]
  apply Complex.ext
  · exact W.trace_value s hs
  · simp
lemma erased_entries (v : n → H) (i₀ : n) {s : Set T} (hs : MeasurableSet s) :
    (fun i j => (W.coeff (v i) (v j)+
      projector (Pi.single i₀ (1 : ℂ)) i j • (W.traceComplex-∑ k, W.coeff (v k) (v k))) s)=
      hilbertErase b v i₀ (W.value s) := by
  have ht : Matrix.trace (hilbertCompress v (W.value s))=
      ((Matrix.trace (hilbertCompress v (W.value s))).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hilbertCompress_psd v (W.positive s hs).1).trace_nonneg).2.symm
  ext i j
  simp only [_root_.add_apply,_root_.smul_apply,_root_.sub_apply,_root_.sum_apply,
    W.coeff_value _ _ _ hs,W.traceComplex_value hs,hilbertErase,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub]
  change _+_*((hilbertTrace b (W.value s) : ℂ)-Matrix.trace (hilbertCompress v (W.value s)))=_
  rw [ht]
  rw [mul_comm]
  simp only [Complex.ofReal_re,hilbertCompress]

def erase (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n) : PositiveMatrixMeasure T n where
  entry i j := W.coeff (v i) (v j)+
    projector (Pi.single i₀ (1 : ℂ)) i j • (W.traceComplex-∑ k, W.coeff (v k) (v k))
  positive s hs := by
    rw [W.erased_entries v i₀ hs]
    exact hilbertErase_psd b v hv i₀ (W.positive s hs)
lemma erase_value (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n)
    {s : Set T} (hs : MeasurableSet s) :
    (W.erase v hv i₀).value s=hilbertErase b v i₀ (W.value s) :=
  W.erased_entries v i₀ hs
lemma erase_traceMeasure (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n) :
    (W.erase v hv i₀).traceMeasure=W.traceMeasure := by
  apply Measure.ext
  intro s hs
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (by
    change (W.erase v hv i₀).traceMeasure.real s=W.traceMeasure.real s
    rw [PositiveMatrixMeasure.traceMeasure_real _ hs,W.erase_value v hv i₀ hs,
      hilbertErase_trace,← W.trace_value s hs])

theorem erase_law (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n) :
    (∀ s, MeasurableSet s → (W.erase v hv i₀).value s=hilbertErase b v i₀ (W.value s)) ∧
      (W.erase v hv i₀).traceMeasure=W.traceMeasure :=
  ⟨fun _ hs => W.erase_value v hv i₀ hs,W.erase_traceMeasure v hv i₀⟩
end PositiveHilbertMeasure

end SecretKey

end

end OAI
