import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCircleIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCircleProjection
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCompactResolvent
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankDiscrete

namespace OAI

/-! # Finite-dimensional complement of the decaying contour space

The decomposition is derived from a contraction plus a finite-rank operator.
Every bounded operator commuting with the time step preserves both pieces.
-/

open Complex Set

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem finiteRange_isCompactOperator (K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap)) :
    IsCompactOperator K := by
  let V := LinearMap.range K.toLinearMap
  let : FiniteDimensional ℂ V := hK
  let A : E →L[ℂ] V := K.codRestrict V (fun x => ⟨x, rfl⟩)
  exact (isCompactOperator_of_locallyCompactSpace_dom A).clm_comp V.subtypeL

theorem finiteRank_contour_decomposition (B K : E →L[ℂ] E)
    (hB : ‖B‖ < 1)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (η : ℝ) (hη : η < 1) :
    ∃ r : ℝ, η < r ∧ 0 < r ∧ r < 1 ∧
      ∃ Q : E →L[ℂ] E, IsIdempotentElem Q ∧
        FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
        (∀ U : E →L[ℂ] E, Commute U (B + K) → Commute U Q) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x : E, Q x = 0 →
          ‖((B + K) ^ n) x‖ ≤ C * r ^ n * ‖x‖ := by
  obtain ⟨r, hBr, hηr, hr1, hres⟩ :=
    finiteRank_exists_resolvent_circle B K hK hB η hη
  have hr : 0 < r := (norm_nonneg B).trans_lt hBr
  let P := circleResolventOperator (B + K) r
  let Q : E →L[ℂ] E := 1 - P
  have hP : P * P = P := circleResolventOperator_idempotent (B + K) hr hres
  have hQ : IsIdempotentElem Q := by
    change (1 - P) * (1 - P) = 1 - P
    rw [mul_sub, mul_one, sub_mul, one_mul, hP, sub_self, sub_zero]
  have hc : IsCompactOperator (show E →L[ℂ] E from P - 1) := by
    have hcK : IsCompactOperator (B + K - B) := by
      simpa only [add_sub_cancel_left] using finiteRange_isCompactOperator K hK
    have hh := circleResolventOperator_sub_isCompact (B + K) B hcK hr.le hres
      (fun z hz => norm_lt_mem_resolvent B (hBr.trans_le hz.ge))
    simpa only [circleResolventOperator_eq_one B hBr] using hh
  have hcQ : IsCompactOperator Q := by
    simpa only [← FunLike.coe_neg, neg_sub, Q] using hc.neg
  obtain ⟨C, hC, hpow⟩ := powers_on_circleResolvent_fixedSpace (B + K) hr.le hres
  refine ⟨r, hηr, hr, hr1, Q, hQ,
    finiteDimensional_range_of_compact_projection Q hQ hcQ, ?_, C, hC, ?_⟩
  · intro U hU
    exact (Commute.one_right U).sub_right
      (circleResolventOperator_commute_of_commute U (B + K) hU hr.le hres)
  · intro n x hx
    apply hpow n x
    change x - P x = 0 at hx
    exact (sub_eq_zero.mp hx).symm

end

end DefocusingNLS

end OAI
