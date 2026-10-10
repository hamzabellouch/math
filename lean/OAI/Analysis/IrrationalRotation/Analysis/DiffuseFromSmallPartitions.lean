import OAI.Analysis.IrrationalRotation.Operators.ProjectionMeetTrace

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projectionAtom_mul_eq_zero_of_trace_lt
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : IsProjectionAtom M p.starProjection) (hq : q.starProjection ∈ M)
    (hlt : (vectorTrace ξ q.starProjection).re < (vectorTrace ξ p.starProjection).re) :
    q.starProjection * p.starProjection = 0 := by
  have hqorth : qᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.one_def] using
      sub_mem (one_mem M) hq
  have hr := ProjectionMeetTrace.meet_projection_mem M p qᗮ hp.1 hqorth
  have hRp : (p ⊓ qᗮ).starProjection * p.starProjection = (p ⊓ qᗮ).starProjection :=
    Submodule.starProjection_comp_starProjection_of_le inf_le_left
  rcases hp.2.2.2 (p ⊓ qᗮ).starProjection hr isStarProjection_starProjection hRp with hzero | heq
  · have hb := ProjectionMeetTrace.vectorTrace_meet_lower_bound M ξ htrace p qᗮ hp.1 hqorth
    have hc : (vectorTrace ξ qᗮ.starProjection).re =
        ‖ξ‖ ^ 2 - (vectorTrace ξ q.starProjection).re := by
      rw [TracialProjectionTransport.vectorTrace_projection_orthogonal]
      simp only [Complex.sub_re]
      norm_cast
    rw [hc, hzero] at hb
    simp only [vectorTrace, zero_apply, inner_zero_right, Complex.zero_re] at hb
    change (inner ℂ ξ (q.starProjection ξ)).re < (inner ℂ ξ (p.starProjection ξ)).re at hlt
    linarith
  · have hpq : p ≤ qᗮ := by
      intro x hx
      have hfix := p.starProjection_eq_self_iff.mpr hx
      rw [← heq] at hfix
      exact ((p ⊓ qᗮ).starProjection_eq_self_iff.mp hfix).2
    ext x
    exact q.starProjection_apply_eq_zero_iff.mpr (hpq (p.starProjection_apply_mem x))

theorem isDiffuse_of_small_trace_separating_families
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Q : Fin n → H →L[ℂ] H),
      (∀ i, Q i ∈ M) ∧ (∀ i, IsStarProjection (Q i)) ∧
      (∀ i, (vectorTrace ξ (Q i)).re < ε) ∧
      (∀ v : H, (∀ i, Q i v = 0) → v = 0)) :
    IsDiffuseVonNeumannAlgebra M := by
  intro P hP
  obtain ⟨hproj, hPeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hP.2.1
  let := hproj
  let : CompleteSpace P.range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.2.1.isIdempotentElem).completeSpace_coe
  have hPpos : P.IsPositive := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    simpa only [hP.2.1.isSelfAdjoint.star_eq, hP.2.1.isIdempotentElem.eq] using
      star_mul_self_nonneg P
  have hnonneg : 0 ≤ (vectorTrace ξ P).re := hPpos.re_inner_nonneg_right ξ
  have hmass : 0 < (vectorTrace ξ P).re := by
    by_contra hn
    have hzre : (vectorTrace ξ P).re = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hz : vectorTrace ξ P = 0 := by
      rw [hPeq, TracialProjectionTransport.vectorTrace_projection] at hzre ⊢
      exact_mod_cast hzre
    exact hP.2.2.1 (hξ.2.2 P hP.1 hPpos hz)
  obtain ⟨n, Q, hQmem, hQproj, hQmass, hQsep⟩ := hpart _ hmass
  have hzero (i : Fin n) : Q i * P = 0 := by
    obtain ⟨hqproj, hQeq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hQproj i)
    let := hqproj
    let : CompleteSpace (Q i).range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hQproj i).isIdempotentElem).completeSpace_coe
    rw [hPeq, hQeq]
    apply projectionAtom_mul_eq_zero_of_trace_lt M ξ hξ.2.1 P.range (Q i).range
    · simpa only [← hPeq] using hP
    · simpa only [← hQeq] using hQmem i
    · simpa only [← hPeq, ← hQeq] using hQmass i
  apply hP.2.2.1
  ext v
  apply hQsep
  intro i
  exact congrArg (fun A : H →L[ℂ] H => A v) (hzero i)

theorem isDiffuse_of_small_trace_partitions
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Q : Fin n → H →L[ℂ] H),
      (∀ i, Q i ∈ M) ∧ (∀ i, IsStarProjection (Q i)) ∧
      (∀ i, (vectorTrace ξ (Q i)).re < ε) ∧ ∑ i, Q i = 1) :
    IsDiffuseVonNeumannAlgebra M := by
  apply isDiffuse_of_small_trace_separating_families M ξ hξ
  intro ε hε
  obtain ⟨n, Q, hmem, hproj, hmass, hsum⟩ := hpart ε hε
  refine ⟨n, Q, hmem, hproj, hmass, ?_⟩
  intro v hv
  have h := congrArg (fun A : H →L[ℂ] H => A v) hsum
  simpa only [sum_apply, hv, Finset.sum_const_zero, one_apply_eq_self] using h.symm
end Invariant233

end

end OAI
