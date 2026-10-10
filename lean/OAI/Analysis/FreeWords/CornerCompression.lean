import Mathlib
import OAI.Analysis.FreeWords.ConcreteCornerFactor
import OAI.Analysis.FreeWords.ConcreteCornerTrace
import OAI.Analysis.FreeWords.LocalCompression

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport KKConcreteCorner

noncomputable section

theorem corner_small_compression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (p : ConcreteAlgebra M) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (x : ι → ConcreteAlgebra M)
    (hs : ∀ i, p*x i*p=x i) (hx : ∀ i, τ.map (x i)=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧ q*p=q ∧
      (τ.map q).re < ε ∧
      ∑ i, (traceNorm τ (q*x i*q))^2 < ε*(τ.map q).re := by
  have hpCLM : IsStarProjection (p : H →L[ℂ] H) := hp.map M.toStarSubalgebra.subtype
  let S : Submodule ℂ H := (p.val : H →ₗ[ℂ] H).range
  let : IsClosed (S : Set H) := ContinuousLinearMap.IsIdempotentElem.isClosed_range hpCLM.isIdempotentElem
  let : CompleteSpace S := IsClosed.completeSpace_coe
  have heq : S.starProjection=p.val := by
    obtain ⟨h,heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hpCLM
    exact heq.symm
  have hmem : S.starProjection ∈ M := heq ▸ p.property
  have hproj : projection S M hmem=p := Subtype.ext heq
  have hproj0 : projection S M hmem≠0 := hproj ▸ hp0
  let C := cornerAlgebra S M
  let σ := cornerTrace S M hmem τ hproj0
  let y : ι → ConcreteAlgebra C := fun i => restrict S M hmem (x i)
  have hy (i : ι) : liftLinear S M hmem (y i)=x i := by
    change liftLinear S M hmem (restrict S M hmem (x i))=x i
    rw [lift_restrict,hproj,hs]
  have hyτ (i : ι) : σ.map (y i)=0 := by
    change (cornerTrace S M hmem τ hproj0).map (y i)=0
    rw [cornerTrace_apply,hy,hx,mul_zero]
  let t : ℝ := (τ.map p).re
  have ht : 0<t := trace_projection_pos τ hp hp0
  let δ : ℝ := min ε (ε/t)
  have hδ : 0<δ := lt_min hε (div_pos hε ht)
  have hδε : δ≤ε := min_le_left _ _
  have hδt : δ≤ε/t := min_le_right _ _
  obtain ⟨Q,hQ,hQ0,hQtrace,hQsmall⟩ := local_small_compression C σ
    (cornerAlgebra_factor S M hmem τ hF hproj0) (cornerAlgebra_diffuse S M hmem hD)
    y hyτ δ hδ
  let q := liftLinear S M hmem Q
  have hq : IsStarProjection q := lift_projection S M hmem Q hQ
  have hq0 : q≠0 := by
    intro hh
    exact hQ0 (lift_injective S M hmem (hh.trans (map_zero _).symm))
  have hqp : q*p=q := by
    rw [← hproj]
    exact (lift_supported S M hmem Q).2
  have htrace : (σ.map Q).re=t⁻¹*(τ.map q).re := by
    change ((cornerTrace S M hmem τ hproj0).map Q).re=_
    rw [cornerTrace_re,hproj]
  have hnorm (i : ι) : (traceNorm σ (Q*y i*Q))^2=t⁻¹*(traceNorm τ (q*x i*q))^2 := by
    change (traceNorm (cornerTrace S M hmem τ hproj0) (Q*y i*Q))^2=_
    rw [cornerTrace_norm_sq,hproj,lift_mul,lift_mul,hy]
  rw [htrace] at hQtrace hQsmall
  simp_rw [hnorm] at hQsmall
  rw [← Finset.mul_sum] at hQsmall
  have hqτ : 0 < (τ.map q).re := trace_projection_pos τ hq hq0
  refine ⟨q,hq,hq0,hqp,?_,?_⟩
  · have h := mul_lt_mul_of_pos_left hQtrace ht
    have hcan : t*(t⁻¹*(τ.map q).re)=(τ.map q).re := by
      rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
    rw [hcan] at h
    have htδ : t*δ≤ε := by
      have hh := (le_div_iff₀ ht).mp hδt
      nlinarith
    exact h.trans_le htδ
  · have hsmall : ∑ i,(traceNorm τ (q*x i*q))^2 < δ*(τ.map q).re := by
      have hi : 0 < t⁻¹ := inv_pos.mpr ht
      have he : δ*(t⁻¹*(τ.map q).re)=t⁻¹*(δ*(τ.map q).re) := by ring
      rw [he] at hQsmall
      nlinarith
    exact hsmall.trans_le (mul_le_mul_of_nonneg_right hδε hqτ.le)

end

end KKMatrixQuantization
end

end OAI
