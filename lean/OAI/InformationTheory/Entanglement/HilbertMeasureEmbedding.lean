import OAI.InformationTheory.Entanglement.HilbertMeasure
import OAI.InformationTheory.Entanglement.HilbertEmbeddingOrder

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder ENNReal MeasureTheory
open ContinuousLinearMap Matrix MeasureTheory
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n : Type} [Fintype n] [DecidableEq n]
omit [CompleteSpace H] in
lemma hilbertTrace_real_smul (b : HilbertBasis ι ℂ H) (c : ℝ) (A : H →L[ℂ] H) :
    hilbertTrace b ((c : ℂ) • A)=c*hilbertTrace b A := by
  simp only [hilbertTrace,_root_.smul_apply,inner_smul_right,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,tsum_mul_left]
omit [CompleteSpace H] [Fintype n] [DecidableEq n] in
lemma hilbertCompress_smul (v : n → H) (c : ℂ) (A : H →L[ℂ] H) :
    hilbertCompress v (c • A)=c • hilbertCompress v A := by
  ext i j
  simp only [hilbertCompress,_root_.smul_apply,inner_smul_right,Matrix.smul_apply,smul_eq_mul]
omit [CompleteSpace H] in
lemma hilbertErase_real_smul (b : HilbertBasis ι ℂ H) (v : n → H) (i₀ : n)
    (c : ℝ) (A : H →L[ℂ] H) :
    hilbertErase b v i₀ ((c : ℂ) • A)=(c : ℂ) • hilbertErase b v i₀ A := by
  simp only [hilbertErase,hilbertCompress_smul,hilbertTrace_real_smul,Matrix.trace_smul,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← mul_sub,Complex.ofReal_mul,smul_add,smul_smul]
lemma finitePositiveTrace_real_smul (b : HilbertBasis ι ℂ H) (c : ℝ) (hc : 0≤c)
    {A : H →L[ℂ] H} (hA : HasFinitePositiveTrace b A) :
    HasFinitePositiveTrace b ((c : ℂ) • A) := by
  refine ⟨?_,?_⟩
  · have he : (c : ℂ) • A=c • A := by ext x; simp
    rw [he]
    exact smul_nonneg hc hA.1
  · simpa only [_root_.smul_apply,inner_smul_right,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hA.2.mul_left c
namespace PositiveMatrixMeasure
omit [DecidableEq n] in
lemma ext_entry {V W : PositiveMatrixMeasure T n} (h : V.entry=W.entry) : V=W := by
  cases V
  cases W
  cases h
  rfl
def hilbertEmbedding (W : PositiveMatrixMeasure T n) (b : HilbertBasis ι ℂ H)
    (v : n → H) (hv : Orthonormal ℂ v) : PositiveHilbertMeasure T H b where
  value s := hilbertEmbed v (W.value s)
  coeff x y := ∑ i, ∑ j, (inner ℂ x (v i)*inner ℂ (v j) y) • W.entry i j
  coeff_value x y s hs := by
    simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,hilbertEmbed_apply,inner_sum,
      inner_smul_right,PositiveMatrixMeasure.value]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  positive s hs := hilbertEmbed_psd_finite b v (W.positive s hs)
  traceMeasure := W.traceMeasure
  traceFinite := inferInstance
  trace_value s hs := by rw [hilbertEmbed_trace b v hv,W.traceMeasure_real hs]
lemma hilbertEmbedding_recovered (W : PositiveMatrixMeasure T n) (b : HilbertBasis ι ℂ H)
    (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n) :
    (W.hilbertEmbedding b v hv).erase v hv i₀=W := by
  have he : ((W.hilbertEmbedding b v hv).erase v hv i₀).entry=W.entry := by
    funext i j
    apply VectorMeasure.ext
    intro s hs
    have h := PositiveHilbertMeasure.erase_value (W.hilbertEmbedding b v hv) v hv i₀ hs
    change _=hilbertErase b v i₀ (hilbertEmbed v (W.value s)) at h
    rw [hilbertErase_embed b v hv i₀] at h
    exact congrArg (fun A : Mat n => A i j) h
  exact ext_entry he

end PositiveMatrixMeasure

end SecretKey

end

end OAI
