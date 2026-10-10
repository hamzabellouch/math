import Mathlib
import OAI.Analysis.WeakInfiniteness.CStarClosedRange

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma nonUnitalStarHom_continuous (φ : A →⋆ₙₐ[ℂ] B) : Continuous φ := by
  let f := (φ : A →ₗ[ℂ] B).mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  exact f.continuous

theorem nonUnitalStarHom_exists_lift_norm_le (φ : A →⋆ₙₐ[ℂ] B) (x : A)
    {M : ℝ} (hM : 0 < M) (hx : ‖φ x‖ ≤ M) :
    ∃ y : A, φ y = φ x ∧ ‖y‖ ≤ M := by
  obtain ⟨y, hy, hyn⟩ := starHom_exists_lift_norm_le (Unitization.starMap φ)
    (x : Unitization ℂ A) hM (by simpa only [Unitization.starMap_inr, Unitization.norm_inr] using hx)
  have hfst : y.fst = 0 := by
    simpa [Unitization.algebraMap_eq_inl] using congrArg (fun z : Unitization ℂ B => z.fst) hy
  have he : (y.snd : Unitization ℂ A) = y := by
    apply Unitization.ext
    · simpa using hfst.symm
    · rfl
  refine ⟨y.snd, ?_, ?_⟩
  · simpa [Unitization.algebraMap_eq_inl] using congrArg (fun z : Unitization ℂ B => z.snd) hy
  · rw [← Unitization.norm_inr (𝕜 := ℂ), he]
    exact hyn

theorem nonUnitalStarHom_isClosed_range (φ : A →⋆ₙₐ[ℂ] B) : IsClosed (Set.range φ) := by
  let f : A →L[ℂ] B := (φ : A →ₗ[ℂ] B).mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  let K := f.ker
  let F : A ⧸ K →L[ℂ] B := K.liftQL f le_rfl
  have hbound : ∀ z : A ⧸ K, ‖z‖ ≤ (1 : ℝ≥0) * ‖F z‖ := by
    intro z
    induction z using Submodule.Quotient.induction_on K with
    | H x =>
      change ‖(Submodule.Quotient.mk x : A ⧸ K)‖ ≤ (1 : ℝ) * ‖φ x‖
      rw [one_mul]
      by_cases hx : φ x = 0
      · have hk : x ∈ K := hx
        rw [(Submodule.Quotient.mk_eq_zero K).mpr hk, norm_zero, hx, norm_zero]
      · obtain ⟨y, hy, hyn⟩ := nonUnitalStarHom_exists_lift_norm_le φ x
          (norm_pos_iff.mpr hx) le_rfl
        have hq : (Submodule.Quotient.mk x : A ⧸ K) = Submodule.Quotient.mk y := by
          apply (Submodule.Quotient.eq K).mpr
          change φ (x - y) = 0
          rw [map_sub, hy, sub_self]
        rw [hq]
        exact (Submodule.Quotient.norm_mk_le K y).trans hyn
  have hclosed := (F.antilipschitz_of_bound hbound).isClosed_range F.uniformContinuous
  have hr : Set.range F = Set.range φ := by
    ext b
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact hr ▸ hclosed

end NonUnital

end WeakPureInfiniteness
end

end OAI
