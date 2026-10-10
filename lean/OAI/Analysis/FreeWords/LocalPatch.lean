import Mathlib
import OAI.Analysis.FreeWords.CenteredCornerCompression
import OAI.Analysis.FreeWords.CornerWeakPowers

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport KKMatrixQuantization

noncomputable section

theorem local_patch
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (p : ConcreteAlgebra M) (hp : IsStarProjection p) (hp0 : p≠0)
    (x : ι → ConcreteAlgebra M) (z : κ → ConcreteAlgebra M)
    (k : κ → ℤ) (hk : ∀ i, k i ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ v : PartialUnitary (ConcreteAlgebra M),
      v.support≠0 ∧ v.support*p=v.support ∧ (τ.map v.support).re<ε ∧
      (∑ i, (traceNorm τ (v.support*x i*v.support-
        ((τ.map p)⁻¹*τ.map (p*x i*p)) • v.support))^2 < ε*(τ.map v.support).re) ∧
      ∀ i, ‖τ.map (v.power (k i)*z i)‖<ε*(τ.map v.support).re := by
  let y (i : ι) := p*x i*p
  have hy (i:ι) : p*y i*p=y i := by
    dsimp only [y]
    simp only [← mul_assoc,hp.isIdempotentElem.eq]
    rw [mul_assoc (p*x i) p p,hp.isIdempotentElem.eq]
  obtain ⟨q,hq,hq0,hqp,hqt,hqs⟩ := corner_centered_compression M τ hF hD p hp hp0 y hy ε hε
  have hpq : p*q=q := by
    have h := congrArg star hqp
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq] using h
  have he (i:ι) : q*y i*q=q*x i*q := by
    dsimp only [y]
    calc
      q*(p*x i*p)*q = (q*p)*x i*(p*q) := by noncomm_ring
      _ = q*x i*q := by rw [hqp,hpq]
  have hqτ : 0<(τ.map q).re := trace_projection_pos τ hq hq0
  obtain ⟨v,hv,hsmall⟩ := corner_weakly_small_powers M τ hF hD q hq hq0 z k hk
    (ε*(τ.map q).re) (mul_pos hε hqτ)
  refine ⟨v,hv ▸ hq0,?_,?_,?_,?_⟩
  · rw [hv]; exact hqp
  · rw [hv]; exact hqt
  · rw [hv]
    simpa only [he] using hqs
  · rw [hv]; exact hsmall

end

end KKLocalPatching
end

end OAI
