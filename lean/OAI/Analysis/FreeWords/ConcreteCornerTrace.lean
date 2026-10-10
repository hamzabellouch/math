import Mathlib
import OAI.Analysis.FreeWords.ConcreteCornerAlgebra
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKConcreteCorner

open KKTraceTransfer KKProjectionSupport

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : Submodule ℂ H) [CompleteSpace S]

variable (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)

variable (τ : FaithfulNormalTrace M) (hp0 : projection S M hp ≠ 0)

theorem extend_positive {x : S →L[ℂ] S} (hx : x.IsPositive) : (extend S x).IsPositive := by
  simpa only [extend,Submodule.adjoint_orthogonalProjectionOnto] using
    hx.adjoint_conj S.orthogonalProjectionOnto

def extendWeak (T : WeakAlgebra (cornerAlgebra S M)) : WeakAlgebra M :=
  ⟨(ContinuousLinearMapWOT.ofCLM S.subtypeL).comp
      (T.val.comp (ContinuousLinearMapWOT.ofCLM S.orthogonalProjectionOnto)),
    (mem_cornerAlgebra_iff S M hp _).mp T.property⟩

theorem extendWeak_continuous : Continuous (extendWeak S M hp) := by
  apply Continuous.subtype_mk
  exact (ContinuousLinearMapWOT.continuous_postcomp (ContinuousLinearMapWOT.ofCLM S.subtypeL)).comp
    ((ContinuousLinearMapWOT.continuous_precomp
      (ContinuousLinearMapWOT.ofCLM S.orthogonalProjectionOnto)).comp continuous_subtype_val)

theorem trace_projection_real : ((τ.map (projection S M hp)).re : ℂ)=τ.map (projection S M hp) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (trace_projection_nonneg τ (projection_isStar' S M hp))).2

def cornerTrace : FaithfulNormalTrace (cornerAlgebra S M) where
  map := (Complex.ofReal (((τ.map (projection S M hp)).re)⁻¹)) • (τ.map.comp (liftLinear S M hp))
  positive x hx := by
    have ht := Complex.nonneg_iff.mp (τ.positive (liftLinear S M hp x) (extend_positive S hx))
    apply Complex.nonneg_iff.mpr
    constructor
    · change 0 ≤ ((((τ.map (projection S M hp)).re)⁻¹ : ℝ) : ℂ).re *
          (τ.map (liftLinear S M hp x)).re -
        ((((τ.map (projection S M hp)).re)⁻¹ : ℝ) : ℂ).im *
          (τ.map (liftLinear S M hp x)).im
      simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_nonneg (inv_nonneg.mpr (trace_projection_pos τ (projection_isStar' S M hp) hp0).le) ht.1
    · change 0=((((τ.map (projection S M hp)).re)⁻¹ : ℝ) : ℂ).re *
          (τ.map (liftLinear S M hp x)).im +
        ((((τ.map (projection S M hp)).re)⁻¹ : ℝ) : ℂ).im *
          (τ.map (liftLinear S M hp x)).re
      rw [← ht.2]
      simp
  normalized := by
    change Complex.ofReal (((τ.map (projection S M hp)).re)⁻¹)*τ.map (liftLinear S M hp 1)=1
    rw [lift_one]
    calc
      _ = Complex.ofReal (((τ.map (projection S M hp)).re)⁻¹)*
          Complex.ofReal ((τ.map (projection S M hp)).re) := by
        congr 1
        exact (trace_projection_real S M hp τ).symm
      _ = 1 := by
        rw [← Complex.ofReal_mul,inv_mul_cancel₀
          (trace_projection_pos τ (projection_isStar' S M hp) hp0).ne',Complex.ofReal_one]
  tracial x y := by
    change _*τ.map (liftLinear S M hp (x*y))=_*τ.map (liftLinear S M hp (y*x))
    rw [lift_mul,lift_mul,τ.tracial]
  faithful x hx ht := by
    have hc : ((((τ.map (projection S M hp)).re)⁻¹ : ℝ) : ℂ)≠0 := by
      exact_mod_cast (inv_ne_zero (trace_projection_pos τ (projection_isStar' S M hp) hp0).ne')
    have hzero := (mul_eq_zero.mp ht).resolve_left hc
    have he := τ.faithful (liftLinear S M hp x) (extend_positive S hx) hzero
    exact lift_injective S M hp (he.trans (map_zero _).symm)
  normal r := by
    have hf : ContinuousOn (fun T : WeakAlgebra (cornerAlgebra S M) =>
        τ.map (weakToAlgebra (extendWeak S M hp T))) {T | ‖T.val.toCLM‖ ≤ r} :=
      (τ.normal r).comp (extendWeak_continuous S M hp).continuousOn (fun T hT =>
        (extend_norm_le S T.val.toCLM).trans hT)
    exact continuousOn_const.mul hf

@[simp] theorem cornerTrace_apply (x : ConcreteAlgebra (cornerAlgebra S M)) :
    (cornerTrace S M hp τ hp0).map x=
      (Complex.ofReal (((τ.map (projection S M hp)).re)⁻¹))*τ.map (liftLinear S M hp x) := rfl

theorem cornerTrace_re (x : ConcreteAlgebra (cornerAlgebra S M)) :
    ((cornerTrace S M hp τ hp0).map x).re=
      ((τ.map (projection S M hp)).re)⁻¹*(τ.map (liftLinear S M hp x)).re := by
  rw [cornerTrace_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem cornerTrace_norm_sq (x : ConcreteAlgebra (cornerAlgebra S M)) :
    (traceNorm (cornerTrace S M hp τ hp0) x)^2=
      ((τ.map (projection S M hp)).re)⁻¹*(traceNorm τ (liftLinear S M hp x))^2 := by
  have h := congrArg Complex.re (traceNorm_sq (cornerTrace S M hp τ hp0) x)
  rw [Complex.ofReal_re,cornerTrace_re,lift_mul,lift_star,← traceNorm_sq,Complex.ofReal_re] at h
  exact h

end

end KKConcreteCorner
end

end OAI
