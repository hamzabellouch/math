import OAI.Analysis.FactorGeneration.PartialUnitaries

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Correct residual-corner trace identity for arbitrary f. The first term
is trace(f*x), not trace(x); they agree when f=1. This is the distinction
at Popa 1308.3982v3 Lemma 3.2, equation (5). -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def residualCorner (f : AlgebraProjection M) (v : PartialUnitary M) (hv : v.support ≤ f) :
    AlgebraProjection M :=
  ⟨f.val-v.support.val,v.support.property.sub_of_mul_eq_right f.property hv⟩

theorem projection_compression_trace (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    τ.trace (p.val*x*p.val) = τ.trace (x*p.val) := by
  rw [τ.trace_mul_comm,← mul_assoc,p.property.isIdempotentElem.eq,τ.trace_mul_comm]

theorem residualCorner_trace (f : AlgebraProjection M) (v : PartialUnitary M)
    (hv : v.support ≤ f) :
    τ.trace (residualCorner f v hv).val = τ.trace f.val-τ.trace v.support.val :=
  trace_sub τ _ _

theorem residualCorner_compression_trace (f : AlgebraProjection M) (v : PartialUnitary M)
    (hv : v.support ≤ f) (x : M.toStarSubalgebra) :
    τ.trace ((residualCorner f v hv).val*x*(residualCorner f v hv).val) =
      τ.trace (f.val*x)-τ.trace (star v.val*x*v.val) := by
  rw [projection_compression_trace]
  change τ.trace (x*(f.val-v.support.val)) = _
  rw [mul_sub,trace_sub,τ.trace_mul_comm x f.val]
  congr 1
  calc τ.trace (x*v.support.val) = τ.trace ((x*v.val)*star v.val) := by
         rw [mul_assoc,v.unitary.final]
    _ = τ.trace (star v.val*x*v.val) := by
      rw [τ.trace_mul_comm]
      simp only [mul_assoc]

theorem residualCorner_positive (f : AlgebraProjection M) (hf : f.val ≠ 0)
    (v : PartialUnitary M) (hv : v.support ≤ f)
    (hsmall : (τ.trace v.support.val).re ≤ (τ.trace f.val).re/4) :
    0 < (τ.trace (residualCorner f v hv).val).re := by
  rw [residualCorner_trace,Complex.sub_re]
  have h := projection_trace_pos τ f.val f.property hf
  linarith

theorem residualCorner_support_ratio (f : AlgebraProjection M) (hf : f.val ≠ 0)
    (v : PartialUnitary M) (hv : v.support ≤ f)
    (hsmall : (τ.trace v.support.val).re ≤ (τ.trace f.val).re/4) :
    (τ.trace v.support.val).re / (τ.trace (residualCorner f v hv).val).re ≤ (1/3 : ℝ) := by
  rw [div_le_iff₀ (residualCorner_positive τ f hf v hv hsmall)]
  rw [residualCorner_trace,Complex.sub_re]
  linarith

/-- This keeps the f-dependent scalar term that cannot be bounded from
global centering alone. -/
theorem residualCorner_scalar_bound (f : AlgebraProjection M) (hf : f.val ≠ 0)
    (v : PartialUnitary M) (hv : v.support ≤ f)
    (hsmall : (τ.trace v.support.val).re ≤ (τ.trace f.val).re/4)
    (x : M.toStarSubalgebra) :
    ‖cornerScalar τ (residualCorner f v hv) x‖ ≤
      (‖τ.trace (f.val*x)‖+‖τ.trace (star v.val*x*v.val)‖) /
        (τ.trace (residualCorner f v hv).val).re := by
  rw [cornerScalar,residualCorner_compression_trace,norm_div,
    projection_trace_real τ (residualCorner f v hv),Complex.norm_real,
    Real.norm_of_nonneg (residualCorner_positive τ f hf v hv hsmall).le]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) (residualCorner_positive τ f hf v hv hsmall).le

end

/-! The justified f=1 scalar estimate in the support-growth argument.
Every estimate is tied to the current partial unitary's actual residual;
there is no arbitrary-corner centering assertion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def unitResidual (v : PartialUnitary M) : AlgebraProjection M :=
  ⟨1-v.support.val,v.support.property.one_sub⟩

theorem unitResidual_trace (v : PartialUnitary M) :
    τ.trace (unitResidual v).val=1-τ.trace v.support.val := by
  rw [unitResidual,trace_sub,τ.trace_one]

theorem unitResidual_compression_trace (v : PartialUnitary M) (x : M.toStarSubalgebra)
    (ht : τ.trace x=0) :
    τ.trace ((unitResidual v).val*x*(unitResidual v).val) = -τ.trace (star v.val*x*v.val) := by
  have h := residualCorner_compression_trace τ ⟨1,IsStarProjection.one _⟩ v
    (show v.support ≤ (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) from one_mul _) x
  simpa only [residualCorner,unitResidual,one_mul,ht,zero_sub] using h

theorem unitResidual_positive (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
    0 < (τ.trace (unitResidual v).val).re := by
  rw [unitResidual_trace,Complex.sub_re,Complex.one_re]
  linarith

/-- A previously controlled length-two moment gives the factor 1/3 in the
current residual's scalar expectation. No new centering premise is inferred. -/
theorem unitResidual_scalar_bound (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmoment : ‖τ.trace (star v.val*x*v.val)‖ ≤ δ*(τ.trace v.support.val).re) :
    ‖cornerScalar τ (unitResidual v) x‖ ≤ δ/3 := by
  rw [cornerScalar,unitResidual_compression_trace τ v x ht,norm_div,norm_neg,
    projection_trace_real τ (unitResidual v),Complex.norm_real,
    Real.norm_of_nonneg (unitResidual_positive τ v hsmall).le]
  rw [div_le_iff₀ (unitResidual_positive τ v hsmall)]
  rw [unitResidual_trace,Complex.sub_re,Complex.one_re]
  nlinarith [mul_le_mul_of_nonneg_left hsmall hδ]

/-- The corresponding actual residual compression bound, once a local
centered L2 estimate has been proved for q. It retains q and its trace. -/
theorem unitResidual_local_L2 (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) (δ η : ℝ) (hδ : 0 ≤ δ)
    (hmoment : ‖τ.trace (star v.val*x*v.val)‖ ≤ δ*(τ.trace v.support.val).re)
    (q : AlgebraProjection M) (hq : q ≤ unitResidual v)
    (hlocal : τ.norm₂ (q.val*cornerCentered τ (unitResidual v) x*q.val) < η*τ.norm₂ q.val) :
    τ.norm₂ (q.val*x*q.val) < (η+δ/3)*τ.norm₂ q.val := by
  have he : q.val*x*q.val = q.val*cornerCentered τ (unitResidual v) x*q.val +
      cornerScalar τ (unitResidual v) x • q.val := by
    rw [compress_cornerCentered τ hq,sub_add_cancel]
  calc τ.norm₂ (q.val*x*q.val) ≤
      τ.norm₂ (q.val*cornerCentered τ (unitResidual v) x*q.val)+
        τ.norm₂ (cornerScalar τ (unitResidual v) x • q.val) := by
          conv_lhs => rw [he]
          exact τ.norm₂_add_le _ _
    _ ≤ τ.norm₂ (q.val*cornerCentered τ (unitResidual v) x*q.val)+δ/3*τ.norm₂ q.val := by
      rw [τ.norm₂_smul]
      have hh := mul_le_mul_of_nonneg_right
        (unitResidual_scalar_bound τ v hsmall x ht δ hδ hmoment)
        (show 0 ≤ τ.norm₂ q.val from norm_nonneg _)
      linarith only [hh]
    _ < (η+δ/3)*τ.norm₂ q.val := by nlinarith only [hlocal]

end Generator.Tracial

end

end OAI
