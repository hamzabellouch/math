import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem pairedEigenvalue_modulus_le_opNorm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) {a b : ℝ} {u v : V}
    (huv : u ≠ 0 ∨ v ≠ 0)
    (hu : A u = a • u - b • v)
    (hv : A v = b • u + a • v) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ ‖A‖ := by
  have hid : ‖A u‖ ^ 2 + ‖A v‖ ^ 2 =
      (a ^ 2 + b ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [hu, hv, norm_sub_sq_real, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hp : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rcases huv with h | h
    · have := norm_pos_iff.mpr h
      positivity
    · have := norm_pos_iff.mpr h
      positivity
  have hAu : ‖A u‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (A u)) (A.le_opNorm u) 2
  have hAv : ‖A v‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (A v)) (A.le_opNorm v) 2
  have hs : a ^ 2 + b ^ 2 ≤ ‖A‖ ^ 2 := by
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith [hid]
  exact (Real.sqrt_le_iff).2 ⟨norm_nonneg A, hs⟩

theorem exists_bound_pairedEigenvalue_modulus
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) :
    ∃ C : ℝ, ∀ (a b : ℝ) (u v : V),
      (u ≠ 0 ∨ v ≠ 0) →
      A u = a • u - b • v →
      A v = b • u + a • v →
      Real.sqrt (a ^ 2 + b ^ 2) ≤ C := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq V E finrank_euclideanSpace_fin.symm
  let B : E →L[ℝ] E := LinearMap.toContinuousLinearMap (e.conj A)
  refine ⟨‖B‖, ?_⟩
  intro a b u v huv hu hv
  apply pairedEigenvalue_modulus_le_opNorm B (u := e u) (v := e v)
  · simpa only [ne_eq, e.map_eq_zero_iff] using huv
  · change e (A (e.symm (e u))) = a • e u - b • e v
    simpa only [e.symm_apply_apply, map_sub, map_smul] using congrArg e hu
  · change e (A (e.symm (e v))) = b • e u + a • e v
    simpa only [e.symm_apply_apply, map_add, map_smul] using congrArg e hv

theorem bddAbove_total_pairedEigenvalue_moduli
    {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
    [∀ n, FiniteDimensional ℝ (V n)]
    (A : ∀ n, V n →ₗ[ℝ] V n) (N : ℕ)
    (hvanish : ∀ n, N < n → Subsingleton (V n)) :
    BddAbove {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : V n,
      (u ≠ 0 ∨ v ≠ 0) ∧
      A n u = a • u - b • v ∧
      A n v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  classical
  choose C hC using fun n => exists_bound_pairedEigenvalue_modulus (A n)
  obtain ⟨M, hM⟩ := (Set.finite_range (fun n : Fin (N + 1) => C n)).bddAbove
  refine ⟨M, ?_⟩
  rintro r ⟨n, a, b, u, v, huv, hu, hv, rfl⟩
  have hn : n < N + 1 := by
    by_contra h
    have hi : N < n := by omega
    let := hvanish n hi
    rcases huv with h | h
    · exact h (Subsingleton.elim _ _)
    · exact h (Subsingleton.elim _ _)
  exact (hC n a b u v huv hu hv).trans (hM ⟨⟨n, hn⟩, rfl⟩)

end Problem340

end

end OAI
