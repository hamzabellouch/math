import OAI.InformationTheory.Entanglement.HilbertEmbedding
import OAI.InformationTheory.Entanglement.PurificationSupport

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open ContinuousLinearMap Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n e : Type} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]
lemma hilbertErase_hermitian_traceClass (b : HilbertBasis ι ℂ H) (v : e → H)
    (hv : Orthonormal ℂ v) (j₀ : e) {T : H →L[ℂ] H} (hT : HermitianTraceClass b T) :
    (hilbertErase b v j₀ T).IsHermitian := by
  obtain ⟨hp,hm⟩ := hermitian_parts_finite b hT
  have he : hilbertErase b v j₀ (posPart T)-hilbertErase b v j₀ (negPart T)=hilbertErase b v j₀ T := by
    rw [← hilbertErase_sub b v j₀ _ _ hp.2 hm.2,CFC.posPart_sub_negPart T hT.1]
  rw [← he]
  exact (hilbertErase_psd b v hv j₀ hp).isHermitian.sub (hilbertErase_psd b v hv j₀ hm).isHermitian

theorem hilbert_canonical_recovery (b : HilbertBasis ι ℂ H) (v : e → H)
    (hv : Orthonormal ℂ v) (j₀ : e) (i₀ : n) (B : Matrix e n ℂ) :
    ∃ F : Map e n, CP F ∧ TracePreserving F ∧
      (∀ {T : H →L[ℂ] H}, HasFinitePositiveTrace b T →
        (F (hilbertErase b v j₀ T)).PosSemidef) ∧
      (∀ T : H →L[ℂ] H, (Matrix.trace (F (hilbertErase b v j₀ T))).re=hilbertTrace b T) ∧
      (∀ {T : H →L[ℂ] H}, HermitianTraceClass b T →
        traceNorm (F (hilbertErase b v j₀ T))≤hilbertTraceNorm b T) ∧
      ∀ A : Mat n, F (hilbertErase b v j₀ (hilbertEmbed v (B*A*Bᴴ)))=
        CFC.sqrt (Bᴴ*B)*A*CFC.sqrt (Bᴴ*B) := by
  obtain ⟨F,hF,hTP,hrec⟩ := finite_purification_recovery i₀ B
  refine ⟨F,hF,hTP,?_,?_,?_,?_⟩
  · intro T hT
    exact cp_positive hF (hilbertErase_psd b v hv j₀ hT)
  · intro T
    rw [hTP,hilbertErase_trace]
  · intro T hT
    exact (traceNorm_cptp F hF hTP (hilbertErase_hermitian_traceClass b v hv j₀ hT)).trans
      (hilbertErase_contract b v hv j₀ hT)
  · intro A
    rw [hilbertErase_embed b v hv]
    exact hrec A

end SecretKey

end

end OAI
