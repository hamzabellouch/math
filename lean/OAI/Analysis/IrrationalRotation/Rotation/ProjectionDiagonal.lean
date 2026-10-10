import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

namespace Invariant233.ProjectionDiagonal

open scoped InnerProduct InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem inner_projection_eq_inner_projected (p : E →L[ℂ] E)
    (hp : IsStarProjection p) (e : E) :
    ⟪p e, e⟫_ℂ = ⟪p e, p e⟫_ℂ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.isSelfAdjoint
  have hidem : p (p e) = p e := by
    exact congrArg (fun A : E →L[ℂ] E => A e) hp.isIdempotentElem
  have h := hsym (p e) e
  change ⟪p (p e), e⟫_ℂ = ⟪p e, p e⟫_ℂ at h
  simpa only [hidem] using h

theorem inner_projection_eq_zero_iff (p : E →L[ℂ] E)
    (hp : IsStarProjection p) (e : E) :
    ⟪p e, e⟫_ℂ = 0 ↔ p e = 0 := by
  rw [inner_projection_eq_inner_projected p hp e, inner_self_eq_zero]

theorem inner_projection_eq_self_iff (p : E →L[ℂ] E)
    (hp : IsStarProjection p) (e : E) :
    ⟪p e, e⟫_ℂ = ⟪e, e⟫_ℂ ↔ p e = e := by
  constructor
  · intro htop
    have hz : ⟪(1 - p) e, e⟫_ℂ = 0 := by
      simp only [sub_apply, one_apply_eq_self, inner_sub_left]
      exact sub_eq_zero.mpr htop.symm
    have he := (inner_projection_eq_zero_iff (1 - p) hp.one_sub e).mp hz
    have he' : e - p e = 0 := by simpa only [sub_apply, one_apply_eq_self] using he
    exact (sub_eq_zero.mp he').symm
  · intro he
    rw [he]

omit [CompleteSpace E] in
theorem transported_vector_fixed {p q D : E →L[ℂ] E}
    (hinv : (1 - q) * D * p = 0) (v : E) :
    q (D (p v)) = D (p v) := by
  have h := congrArg (fun A : E →L[ℂ] E => A v) hinv
  have hz : D (p v) - q (D (p v)) = 0 := by
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, zero_apply] using h
  exact (sub_eq_zero.mp hz).symm

theorem zero_diagonal_propagates_backward {p q D : E →L[ℂ] E}
    (hq : IsStarProjection q)
    {e : E} {c : ℂ} (hc : c ≠ 0) (hDe : D.adjoint e = c • e)
    (hinv : (1 - q) * D * p = 0) (hqzero : ⟪q e, e⟫_ℂ = 0) :
    ⟪p e, e⟫_ℂ = 0 := by
  have hqe : q e = 0 := (inner_projection_eq_zero_iff q hq e).mp hqzero
  have hqsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hq.isSelfAdjoint
  have hfixed := transported_vector_fixed hinv e
  have hz : ⟪D (p e), e⟫_ℂ = 0 := by
    calc
      ⟪D (p e), e⟫_ℂ = ⟪q (D (p e)), e⟫_ℂ := by rw [hfixed]
      _ = ⟪D (p e), q e⟫_ℂ := hqsym _ _
      _ = 0 := by rw [hqe]; simp
  rw [← D.adjoint_inner_right, hDe, inner_smul_right] at hz
  exact (mul_eq_zero.mp hz).resolve_left hc

omit [CompleteSpace E] in
theorem fixed_vector_propagates_forward {p q D : E →L[ℂ] E}
    {e : E} {c : ℂ} (hc : c ≠ 0) (hDe : D e = c • e)
    (hinv : (1 - q) * D * p = 0) (hpe : p e = e) : q e = e := by
  have hfixed := transported_vector_fixed hinv e
  rw [hpe, hDe, map_smul] at hfixed
  exact (smul_right_injective E hc) hfixed

theorem top_diagonal_propagates_forward {p q D : E →L[ℂ] E}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {e : E} {c : ℂ} (hc : c ≠ 0) (hDe : D e = c • e)
    (hinv : (1 - q) * D * p = 0) (hptop : ⟪p e, e⟫_ℂ = ⟪e, e⟫_ℂ) :
    ⟪q e, e⟫_ℂ = ⟪e, e⟫_ℂ := by
  apply (inner_projection_eq_self_iff q hq e).mpr
  exact fixed_vector_propagates_forward hc hDe hinv
    ((inner_projection_eq_self_iff p hp e).mp hptop)

end Invariant233.ProjectionDiagonal

end OAI
