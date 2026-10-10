import OAI.InformationTheory.Entanglement.HilbertTrace
import OAI.InformationTheory.Entanglement.TraceContractivity

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open ContinuousLinearMap Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n : Type} [Fintype n] [DecidableEq n]

def hilbertCompress (v : n → H) (T : H →L[ℂ] H) : Mat n :=
  fun i j => inner ℂ (v i) (T (v j))
omit [Fintype n] [DecidableEq n] in
lemma hilbertCompress_hermitian (v : n → H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    (hilbertCompress v T).IsHermitian := by
  ext i j
  change star (inner ℂ (v j) (T (v i)))=inner ℂ (v i) (T (v j))
  change (starRingEnd ℂ) (inner ℂ (v j) (T (v i)))=inner ℂ (v i) (T (v j))
  rw [inner_conj_symm]
  exact (isSelfAdjoint_iff_isSymmetric.mp hT) _ _
omit [DecidableEq n] in
lemma hilbertCompress_psd (v : n → H) {T : H →L[ℂ] H} (hT : 0≤T) :
    (hilbertCompress v T).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hilbertCompress_hermitian v hT.isSelfAdjoint) ?_
  intro x
  have h := (nonneg_iff_isPositive.mp hT).inner_nonneg_right (∑ i, x i • v i)
  simp only [map_sum,map_smul,inner_sum,sum_inner,inner_smul_left,inner_smul_right,Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simpa only [hilbertCompress,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,Finset.sum_mul,
    mul_assoc,mul_left_comm,mul_comm,RCLike.star_def] using h

def hilbertErase (b : HilbertBasis ι ℂ H) (v : n → H) (i₀ : n)
    (T : H →L[ℂ] H) : Mat n :=
  hilbertCompress v T+((hilbertTrace b T-(Matrix.trace (hilbertCompress v T)).re : ℝ) : ℂ) • projector (Pi.single i₀ 1)
lemma hilbertErase_psd (b : HilbertBasis ι ℂ H) (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n)
    {T : H →L[ℂ] H} (hT : HasFinitePositiveTrace b T) :
    (hilbertErase b v i₀ T).PosSemidef := by
  apply (hilbertCompress_psd v hT.1).add
  apply (Matrix.posSemidef_vecMulVec_self_star _).smul
  rw [Complex.nonneg_iff]
  refine ⟨sub_nonneg.mpr ?_,rfl⟩
  simpa only [Matrix.trace,Matrix.diag,hilbertCompress,Complex.re_sum] using
    positive_finite_compression_trace b hT v hv Finset.univ

lemma pure_coordinate_trace (i₀ : n) :
    Matrix.trace (projector (Pi.single i₀ (1 : ℂ)))=1 := by
  simp [projector,Matrix.trace,Matrix.diag,Matrix.vecMulVec,Pi.single_apply]
omit [CompleteSpace H] in
lemma hilbertErase_trace (b : HilbertBasis ι ℂ H) (v : n → H) (i₀ : n) (T : H →L[ℂ] H) :
    (Matrix.trace (hilbertErase b v i₀ T)).re=hilbertTrace b T := by
  rw [hilbertErase,Matrix.trace_add,Matrix.trace_smul,pure_coordinate_trace]
  simp only [smul_eq_mul,mul_one,Complex.add_re,Complex.ofReal_re]
  ring
omit [CompleteSpace H] [Fintype n] [DecidableEq n] in
lemma hilbertCompress_sub (v : n → H) (A B : H →L[ℂ] H) :
    hilbertCompress v (A-B)=hilbertCompress v A-hilbertCompress v B := by
  ext i j
  simp only [hilbertCompress,_root_.sub_apply,inner_sub_right,Matrix.sub_apply]
omit [CompleteSpace H] in
lemma hilbertErase_sub (b : HilbertBasis ι ℂ H) (v : n → H) (i₀ : n) (A B : H →L[ℂ] H)
    (hA : Summable (fun i => (inner ℂ (b i) (A (b i))).re))
    (hB : Summable (fun i => (inner ℂ (b i) (B (b i))).re)) :
    hilbertErase b v i₀ (A-B)=hilbertErase b v i₀ A-hilbertErase b v i₀ B := by
  simp only [hilbertErase,hilbertCompress_sub,hilbertTrace_sub b A B hA hB,
    Matrix.trace_sub,Complex.sub_re,Complex.ofReal_sub,sub_smul]
  abel

theorem hilbertErase_contract (b : HilbertBasis ι ℂ H) (v : n → H)
    (hv : Orthonormal ℂ v) (i₀ : n) {T : H →L[ℂ] H}
    (hT : HermitianTraceClass b T) :
    traceNorm (hilbertErase b v i₀ T)≤hilbertTraceNorm b T := by
  obtain ⟨hp,hm⟩ := hermitian_parts_finite b hT
  calc
    traceNorm (hilbertErase b v i₀ T)=traceNorm
        (hilbertErase b v i₀ (posPart T)-hilbertErase b v i₀ (negPart T)) := by
      rw [← hilbertErase_sub b v i₀ _ _ hp.2 hm.2,CFC.posPart_sub_negPart T hT.1]
    _ ≤ traceNorm (hilbertErase b v i₀ (posPart T))+traceNorm (hilbertErase b v i₀ (negPart T)) :=
      traceNorm_sub_le _ _
    _ = hilbertTrace b (posPart T)+hilbertTrace b (negPart T) := by
      rw [traceNorm_of_psd (hilbertErase_psd b v hv i₀ hp),
        traceNorm_of_psd (hilbertErase_psd b v hv i₀ hm),hilbertErase_trace,hilbertErase_trace]
    _ = hilbertTraceNorm b T := (hilbertTraceNorm_jordan b hT).symm

end SecretKey

end

end OAI
