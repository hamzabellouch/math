import OAI.Analysis.FiniteFactor.Diffuse.OperatorSupport
import Mathlib.Analysis.CStarAlgebra.Basic

namespace OAI

noncomputable section
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_vector_trace (v:H) {p:H→L[ℂ]H} (hp:IsStarProjection p) :
    inner ℂ v (p v)=(‖p v‖:ℂ)^2 := by
  have he : (star p)*(p)=p := by rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  calc
    inner ℂ v (p v)=inner ℂ v ((star p) (p v)) := congrArg (fun A:H→L[ℂ]H=>inner ℂ v (A v)) he.symm
    _ = _ := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      norm_cast

lemma projection_vector_trace_nonneg (v:H) {p:H→L[ℂ]H} (hp:IsStarProjection p) :
    0≤(inner ℂ v (p v)).re := by
  rw [projection_vector_trace v hp]
  simp only [←Complex.ofReal_pow,Complex.ofReal_re]
  positivity

lemma projection_difference {p q:H→L[ℂ]H} (hp:IsStarProjection p) (hq:IsStarProjection q)
    (hqp:q*p=q) : IsStarProjection (p-q) := by
  have hpq:p*q=q := by
    have hh:=congrArg star hqp
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq] using hh
  apply isStarProjection_iff'.mpr
  constructor
  · calc
      (p-q)*(p-q)=p*p-p*q-q*p+q*q := by noncomm_ring
      _ = p-q := by rw [hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq,hqp]; abel
  · simp only [star_sub,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq]

lemma projection_vector_trace_mono (v:H) {p q:H→L[ℂ]H}
    (hp:IsStarProjection p) (hq:IsStarProjection q) (hqp:q*p=q) :
    (inner ℂ v (q v)).re≤(inner ℂ v (p v)).re := by
  have hh:=projection_vector_trace_nonneg v (projection_difference hp hq hqp)
  change 0≤(inner ℂ v (p v-q v)).re at hh
  rw [inner_sub_right,Complex.sub_re] at hh
  linarith

end Nonhyperlinear.Diffuseness

end

end OAI
