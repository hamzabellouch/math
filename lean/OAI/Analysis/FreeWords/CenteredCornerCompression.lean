import Mathlib
import OAI.Analysis.FreeWords.CornerCompression

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport

noncomputable section

theorem corner_centered_compression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (p : ConcreteAlgebra M) (hp : IsStarProjection p) (hp0 : p≠0)
    (x : ι → ConcreteAlgebra M) (hs : ∀ i, p*x i*p=x i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q≠0 ∧ q*p=q ∧ (τ.map q).re<ε ∧
      ∑ i, (traceNorm τ (q*x i*q-((τ.map p)⁻¹*τ.map (x i)) • q))^2 < ε*(τ.map q).re := by
  let c (i:ι) : ℂ := (τ.map p)⁻¹*τ.map (x i)
  let y (i:ι) : ConcreteAlgebra M := x i-c i • p
  have hy (i:ι) : p*y i*p=y i := by
    dsimp only [y]
    rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hp.isIdempotentElem.eq,
      hp.isIdempotentElem.eq,hs]
  have hτp : τ.map p ≠ 0 := trace_projection_ne_zero τ hp hp0
  have hyτ (i:ι) : τ.map (y i)=0 := by
    change τ.map (x i-c i • p)=0
    rw [map_sub,map_smul,smul_eq_mul,sub_eq_zero]
    dsimp only [c]
    field_simp
  obtain ⟨q,hq,hq0,hqp,hqt,hqs⟩ := corner_small_compression M τ hF hD p hp hp0 y hy hyτ ε hε
  refine ⟨q,hq,hq0,hqp,hqt,?_⟩
  have he (i:ι) : q*y i*q=q*x i*q-((τ.map p)⁻¹*τ.map (x i)) • q := by
    dsimp only [y,c]
    rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hqp,hq.isIdempotentElem.eq]
  simpa only [he] using hqs

end

end KKMatrixQuantization
end

end OAI
