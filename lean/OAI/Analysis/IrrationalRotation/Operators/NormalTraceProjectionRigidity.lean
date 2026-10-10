import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic

namespace OAI

noncomputable section
namespace Invariant233.NormalTraceProjectionRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem trace_im_eq_zero (τ : TracialState M) {p : M}
    (hp : IsStarProjection (p : H →L[ℂ] H)) : (τ p).im = 0 := by
  have hstar : star p = p := Subtype.ext hp.isSelfAdjoint.star_eq
  have heq : star (τ p) = τ p := (τ.map_star p).symm.trans (congrArg τ hstar)
  have him := congrArg Complex.im heq
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

theorem trace_re_nonneg (τ : TracialState M) {p : M}
    (hp : IsStarProjection (p : H →L[ℂ] H)) : 0 ≤ (τ p).re := by
  have hstar : star p = p := Subtype.ext hp.isSelfAdjoint.star_eq
  have hmul : p * p = p := Subtype.ext hp.isIdempotentElem.eq
  simpa only [hstar, hmul] using τ.positive p

theorem trace_re_eq_zero_iff (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) {p : M}
    (hp : IsStarProjection (p : H →L[ℂ] H)) : (τ p).re = 0 ↔ p = 0 := by
  constructor
  · intro hz
    apply hτ.1 p (ContinuousLinearMap.IsPositive.of_isStarProjection hp)
    exact Complex.ext hz (trace_im_eq_zero τ hp)
  · rintro rfl
    simp only [map_zero, Complex.zero_re]

theorem trace_mono (τ : TracialState M) {p q : M}
    (hp : IsStarProjection (p : H →L[ℂ] H))
    (hq : IsStarProjection (q : H →L[ℂ] H))
    (hpq : (p : H →L[ℂ] H) * (q : H →L[ℂ] H) = p) :
    (τ p).re ≤ (τ q).re := by
  have hdiff : IsStarProjection ((q - p : M) : H →L[ℂ] H) :=
    hp.sub_of_mul_eq_left hq hpq
  have hnonneg := trace_re_nonneg τ hdiff
  change 0 ≤ (τ.toContinuousLinearMap (q - p)).re at hnonneg
  rw [map_sub, Complex.sub_re] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem trace_re_eq_iff_of_nested (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) {p q : M}
    (hp : IsStarProjection (p : H →L[ℂ] H))
    (hq : IsStarProjection (q : H →L[ℂ] H))
    (hpq : (p : H →L[ℂ] H) * (q : H →L[ℂ] H) = p) :
    (τ p).re = (τ q).re ↔ p = q := by
  constructor
  · intro heq
    have hdiff : IsStarProjection ((q - p : M) : H →L[ℂ] H) :=
      hp.sub_of_mul_eq_left hq hpq
    have hz : (τ (q - p)).re = 0 := by
      rw [map_sub, Complex.sub_re, heq, sub_self]
    exact (sub_eq_zero.mp ((trace_re_eq_zero_iff τ hτ hdiff).mp hz)).symm
  · rintro rfl
    rfl

theorem trace_re_eq_one_iff (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) {p : M}
    (hp : IsStarProjection (p : H →L[ℂ] H)) : (τ p).re = 1 ↔ p = 1 := by
  have hone : (τ (1 : M)).re = 1 := by rw [τ.map_one]; rfl
  rw [← hone]
  exact trace_re_eq_iff_of_nested τ hτ hp (IsStarProjection.one _) (mul_one _)

theorem trace_mem_Ioo_iff (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) {p : M}
    (hp : IsStarProjection (p : H →L[ℂ] H)) :
    (τ p).re ∈ Set.Ioo (0 : ℝ) 1 ↔ p ≠ 0 ∧ p ≠ 1 := by
  have hlo := trace_re_nonneg τ hp
  have hhi : (τ p).re ≤ 1 := by
    simpa only [τ.map_one, Complex.one_re] using
      trace_mono τ (q := (1 : M)) hp (IsStarProjection.one _) (mul_one (p : H →L[ℂ] H))
  constructor
  · intro h
    exact ⟨fun hz => (ne_of_gt h.1) ((trace_re_eq_zero_iff τ hτ hp).mpr hz),
      fun ho => (ne_of_lt h.2) ((trace_re_eq_one_iff τ hτ hp).mpr ho)⟩
  · rintro ⟨hz, ho⟩
    exact ⟨lt_of_le_of_ne hlo (Ne.symm (fun h => hz ((trace_re_eq_zero_iff τ hτ hp).mp h))),
      lt_of_le_of_ne hhi (fun h => ho ((trace_re_eq_one_iff τ hτ hp).mp h))⟩

theorem nontrivial_iff_of_trace_eq (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) {p q : M}
    (hp : IsStarProjection (p : H →L[ℂ] H))
    (hq : IsStarProjection (q : H →L[ℂ] H)) (htrace : τ p = τ q) :
    (p ≠ 0 ∧ p ≠ 1) ↔ (q ≠ 0 ∧ q ≠ 1) := by
  rw [← trace_mem_Ioo_iff τ hτ hp, ← trace_mem_Ioo_iff τ hτ hq, htrace]

end Invariant233.NormalTraceProjectionRigidity

end

end OAI
