import OAI.Analysis.IrrationalRotation.Operators.TracialFiniteness
import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic

namespace OAI

noncomputable section
namespace Invariant233.ProjectionTraceRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem vectorTrace_eq_norm_sq (ξ : H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) : vectorTrace ξ p = (‖p ξ‖ ^ 2 : ℂ) := by
  have hpp : p.adjoint * p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]
  calc
    vectorTrace ξ p = inner ℂ ξ ((p.adjoint * p) ξ) := by rw [hpp]; rfl
    _ = inner ℂ (p ξ) (p ξ) := by
      change inner ℂ ξ (p.adjoint (p ξ)) = _
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = _ := inner_self_eq_norm_sq_to_K _

theorem trace_gap_eq_norm_sq (ξ : H) {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    (vectorTrace ξ q).re - (vectorTrace ξ p).re = ‖(q - p) ξ‖ ^ 2 := by
  have h := congrArg Complex.re (vectorTrace_eq_norm_sq ξ (hp.sub_of_mul_eq_left hq hpq))
  simpa only [vectorTrace, sub_apply, inner_sub_right, Complex.sub_re,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem trace_mono (ξ : H) {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    (vectorTrace ξ p).re ≤ (vectorTrace ξ q).re := by
  have h := trace_gap_eq_norm_sq ξ hp hq hpq
  nlinarith [sq_nonneg ‖(q - p) ξ‖]

variable {M : VonNeumannAlgebra H} {ξ : H}

theorem trace_re_eq_zero_iff (hξ : IsFaithfulTracialVector M ξ)
    {p : H →L[ℂ] H} (hmem : p ∈ M) (hp : IsStarProjection p) :
    (vectorTrace ξ p).re = 0 ↔ p = 0 := by
  constructor
  · intro hzero
    apply hξ.2.2 p hmem (ContinuousLinearMap.IsPositive.of_isStarProjection hp)
    rw [vectorTrace_eq_norm_sq ξ hp] at hzero ⊢
    norm_cast at hzero ⊢
  · rintro rfl
    simp [vectorTrace]

theorem trace_re_eq_iff_of_nested (hξ : IsFaithfulTracialVector M ξ)
    {p q : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    (vectorTrace ξ p).re = (vectorTrace ξ q).re ↔ p = q := by
  constructor
  · intro heq
    apply hξ.projection_eq_of_trace_eq hpm hqm hp hq hpq
    apply Complex.ext heq
    rw [vectorTrace_eq_norm_sq ξ hp, vectorTrace_eq_norm_sq ξ hq]
    simp only [← Complex.ofReal_pow, Complex.ofReal_im]
  · rintro rfl
    rfl

theorem trace_eq_iff_of_nested (hξ : IsFaithfulTracialVector M ξ)
    {p q : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    vectorTrace ξ p = vectorTrace ξ q ↔ p = q := by
  constructor
  · intro h
    exact (trace_re_eq_iff_of_nested hξ hpm hqm hp hq hpq).mp (congrArg Complex.re h)
  · rintro rfl
    rfl

theorem trace_lt_of_nested_ne (hξ : IsFaithfulTracialVector M ξ)
    {p q : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = p) (hne : p ≠ q) :
    (vectorTrace ξ p).re < (vectorTrace ξ q).re :=
  lt_of_le_of_ne (trace_mono ξ hp hq hpq)
    (fun h => hne ((trace_re_eq_iff_of_nested hξ hpm hqm hp hq hpq).mp h))

theorem trace_re_eq_one_iff (hξ : IsFaithfulTracialVector M ξ)
    {p : H →L[ℂ] H} (hmem : p ∈ M) (hp : IsStarProjection p) :
    (vectorTrace ξ p).re = 1 ↔ p = 1 := by
  have hone : (vectorTrace ξ (1 : H →L[ℂ] H)).re = 1 := by
    rw [vectorTrace_eq_norm_sq ξ (IsStarProjection.one _)]
    simp [hξ.1]
  rw [← hone]
  exact trace_re_eq_iff_of_nested hξ hmem (one_mem M) hp (IsStarProjection.one _) (mul_one p)

theorem trivial_iff_of_trace_eq (hξ : IsFaithfulTracialVector M ξ)
    {p q : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : vectorTrace ξ p = vectorTrace ξ q) :
    (p = 0 ∨ p = 1) ↔ (q = 0 ∨ q = 1) := by
  have hreal := congrArg Complex.re htrace
  rw [← trace_re_eq_zero_iff hξ hpm hp, ← trace_re_eq_one_iff hξ hpm hp,
    ← trace_re_eq_zero_iff hξ hqm hq, ← trace_re_eq_one_iff hξ hqm hq, hreal]

end Invariant233.ProjectionTraceRigidity

end

end OAI
