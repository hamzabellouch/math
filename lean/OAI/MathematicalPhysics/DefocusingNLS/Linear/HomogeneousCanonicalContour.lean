import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourDecomposition

namespace OAI

/-! # Canonical identity and eigenvalue exclusion for the contour complement

The identity retained here makes the already-constructed finite-dimensional
complement available for generator eigenvalue classification.
-/

namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem contourComplement_eigenvector_modulus (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 < r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T)
    {lam : ℂ} {u : E} (hu : u ≠ 0) (heigen : T u = lam • u)
    (hfix : (1 - circleResolventOperator T r) u = u) : r < ‖lam‖ := by
  by_contra! hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hP := circleResolventOperator_eigenvector_inside T hr hres heigen hlt
    change u - circleResolventOperator T r u = u at hfix
    rw [hP, sub_self] at hfix
    exact hu hfix.symm
  · let A : E →L[ℂ] E := algebraMap ℂ (E →L[ℂ] E) lam - T
    have hA : IsUnit A := hres lam heq
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
    apply hu
    apply hinj
    change lam • u - T u = A 0
    rw [heigen, sub_self, map_zero]

theorem finiteRank_canonical_contour_decomposition (B K : E →L[ℂ] E)
    (hB : ‖B‖ < 1)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (η : ℝ) (hη : η < 1) :
    ∃ r : ℝ, η < r ∧ 0 < r ∧ r < 1 ∧
      (∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ (B + K)) ∧
      ∃ Q : E →L[ℂ] E, Q = 1 - circleResolventOperator (B + K) r ∧
        IsIdempotentElem Q ∧ FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
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
  refine ⟨r, hηr, hr, hr1, hres, Q, rfl, hQ,
    finiteDimensional_range_of_compact_projection Q hQ hcQ, ?_, C, hC, ?_⟩
  · intro U hU
    exact (Commute.one_right U).sub_right
      (circleResolventOperator_commute_of_commute U (B + K) hU hr.le hres)
  · intro n x hx
    apply hpow n x
    change x - P x = 0 at hx
    exact (sub_eq_zero.mp hx).symm

end DefocusingNLS

end OAI
