import OAI.Analysis.IrrationalRotation.Operators.TracialProjectionTransport
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

noncomputable section
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorTrace_projection_re_pos_iff
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P) :
    0 < (vectorTrace ξ P).re ↔ P ≠ 0 := by
  obtain ⟨hproj, hPeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  let := hproj
  have hPpos : P.IsPositive := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    simpa only [hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq] using star_mul_self_nonneg P
  have hnonneg : 0 ≤ (vectorTrace ξ P).re := hPpos.re_inner_nonneg_right ξ
  constructor
  · intro hpos hz
    subst P
    simp [vectorTrace] at hpos
  · intro hne
    by_contra hn
    have hzre : (vectorTrace ξ P).re = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hz : vectorTrace ξ P = 0 := by
      rw [hPeq, TracialProjectionTransport.vectorTrace_projection] at hzre ⊢
      exact_mod_cast hzre
    exact hne (hξ.2.2 P hPm hPpos hz)

theorem vectorTrace_projection_re_lt_one_iff
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P) :
    (vectorTrace ξ P).re < 1 ↔ P ≠ 1 := by
  have hnorm : (inner ℂ ξ ξ).re = 1 := by
    calc
      _ = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
      _ = 1 := by rw [hξ.1, one_pow]
  have hc : (vectorTrace ξ (1 - P)).re = 1 - (vectorTrace ξ P).re := by
    simp only [vectorTrace, sub_apply, one_apply_eq_self, inner_sub_right, Complex.sub_re, hnorm]
  have h := vectorTrace_projection_re_pos_iff M ξ hξ (1 - P)
    (sub_mem (one_mem M) hPm) hP.one_sub
  rw [hc] at h
  constructor
  · intro hp
    have hn := h.mp (by linarith)
    intro heq
    exact hn (by rw [heq, sub_self])
  · intro hp
    have hn : (1 : H →L[ℂ] H) - P ≠ 0 := by
      intro hz
      exact hp (sub_eq_zero.mp hz).symm
    have := h.mpr hn
    linarith

theorem vectorTrace_projection_between_zero_one_iff
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P) :
    (0 < (vectorTrace ξ P).re ∧ (vectorTrace ξ P).re < 1) ↔ (P ≠ 0 ∧ P ≠ 1) :=
  and_congr (vectorTrace_projection_re_pos_iff M ξ hξ P hPm hP)
    (vectorTrace_projection_re_lt_one_iff M ξ hξ P hPm hP)

theorem hasOnlyTrivialInvariantProjections_iff_no_intermediate_trace
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →L[ℂ] H) :
    HasOnlyTrivialInvariantProjections M T ↔
      ∀ P : H →L[ℂ] H, P ∈ M → IsStarProjection P → (1 - P) * T * P = 0 →
        ¬ (0 < (vectorTrace ξ P).re ∧ (vectorTrace ξ P).re < 1) := by
  constructor
  · intro h P hPm hP hinv hm
    have hn := (vectorTrace_projection_between_zero_one_iff M ξ hξ P hPm hP).mp hm
    rcases h P hPm hP hinv with hz | ho
    · exact hn.1 hz
    · exact hn.2 ho
  · intro h P hPm hP hinv
    by_cases hz : P = 0
    · exact Or.inl hz
    · right
      by_contra ho
      exact h P hPm hP hinv
        ((vectorTrace_projection_between_zero_one_iff M ξ hξ P hPm hP).mpr ⟨hz, ho⟩)
end Invariant233

end

end OAI
