import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Geometry.NodalSets.Spectral.FiniteVariationalEigenframe

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem subspace_nonzero_orthogonal_constraints {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (hV : N < Module.finrank ℝ V) (e : Fin N → E) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∀ i, inner ℝ (e i) x = 0 := by
  let L : V →ₗ[ℝ] (Fin N → ℝ) :=
    LinearMap.pi (fun i ↦ (innerSL ℝ (e i)).toLinearMap.comp V.subtype)
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hV)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨x,x.property,fun h ↦ hx0 (Subtype.ext h),?_⟩
  intro i
  exact congrFun (LinearMap.mem_ker.mp hx) i

theorem orthonormal_eigenframe_quadratic_lower {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]
    (T : E →L[ℝ] E) (e : I → E) (mu : I → ℝ)
    (he : Orthonormal ℝ e) (heig : ∀ i, T (e i) = mu i • e i)
    (a : ℝ) (ha : ∀ i, a ≤ mu i) (x : E)
    (hx : x ∈ Submodule.span ℝ (range e)) :
    a * ‖x‖^2 ≤ inner ℝ (T x) x := by
  classical
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hn : ‖∑ i, c i • e i‖^2 = ∑ i, c i^2 := by
    rw [← real_inner_self_eq_norm_sq,sum_inner]
    simp_rw [inner_smul_left_eq_smul,smul_eq_mul,he.inner_right_fintype c,pow_two]
  have hq : inner ℝ (T (∑ i, c i • e i)) (∑ i, c i • e i) =
      ∑ i, mu i * c i^2 := by
    rw [map_sum,sum_inner]
    simp_rw [map_smul,heig,inner_smul_left_eq_smul,smul_eq_mul,he.inner_right_fintype c]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn,hq,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (ha i) (sq_nonneg (c i)))

theorem finite_eigenframe_minmax {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (T : E →L[ℝ] E) (e : Fin (N+1) → E) (mu : Fin (N+1) → ℝ)
    (he : Orthonormal ℝ e) (heig : ∀ i, T (e i) = mu i • e i)
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x = 0) →
      inner ℝ (T x) x ≤ mu i * ‖x‖^2) :
    (∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
      ∀ x ∈ V, mu (Fin.last N) * ‖x‖^2 ≤ inner ℝ (T x) x) ∧
    (∀ V : Submodule ℝ E, FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ inner ℝ (T x) x ≤ mu (Fin.last N) * ‖x‖^2) := by
  constructor
  · refine ⟨Submodule.span ℝ (range e),FiniteDimensional.span_of_finite ℝ (finite_range e),?_,?_⟩
    · simpa using finrank_span_eq_card he.linearIndependent
    · exact orthonormal_eigenframe_quadratic_lower T e mu he heig (mu (Fin.last N))
        (fun i ↦ hanti (Fin.le_last i))
  · intro V hV hdim
    let := hV
    obtain ⟨x,hx,hx0,ho⟩ := subspace_nonzero_orthogonal_constraints V (by omega)
      (fun i : Fin N ↦ e i.castSucc)
    refine ⟨x,hx,hx0,hmax (Fin.last N) x ?_⟩
    intro j hj
    have hjN : j.val < N := hj
    have hh := ho ⟨j.val,hjN⟩
    exact hh

end
end Yau.Analysis

end OAI
