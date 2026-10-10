import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

lemma starHom_continuous {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : Continuous φ := by
  let f := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  exact f.continuous

private def clipScale (M t : ℝ) : ℝ := M / Real.sqrt (max (M ^ 2) t)

private lemma clipScale_den_pos {M : ℝ} (hM : 0 < M) (t : ℝ) :
    0 < Real.sqrt (max (M ^ 2) t) :=
  Real.sqrt_pos.mpr ((sq_pos_of_pos hM).trans_le (le_max_left _ _))

private lemma continuous_clipScale {M : ℝ} (hM : 0 < M) : Continuous (clipScale M) := by
  exact continuous_const.div
    (Real.continuous_sqrt.comp (continuous_const.max continuous_id))
    (fun t => (clipScale_den_pos hM t).ne')

private lemma clipScale_eq_one {M t : ℝ} (hM : 0 < M) (ht : t ≤ M ^ 2) :
    clipScale M t = 1 := by
  simp [clipScale, max_eq_left ht, Real.sqrt_sq hM.le, hM.ne']

private lemma clipScale_bound {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    |clipScale M t * t * clipScale M t| ≤ M ^ 2 := by
  have hd := clipScale_den_pos hM t
  have hs : (Real.sqrt (max (M ^ 2) t)) ^ 2 = max (M ^ 2) t :=
    Real.sq_sqrt ((sq_nonneg M).trans (le_max_left _ _))
  have hf : 0 ≤ clipScale M t := div_nonneg hM.le hd.le
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hf ht) hf)]
  unfold clipScale
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  field_simp
  nlinarith [le_max_right (M ^ 2) t]

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]

theorem starHom_exists_lift_norm_le (φ : A →⋆ₐ[ℂ] B) (x : A)
    {M : ℝ} (hM : 0 < M) (hx : ‖φ x‖ ≤ M) :
    ∃ y : A, φ y = φ x ∧ ‖y‖ ≤ M := by
  let a := star x * x
  let f := clipScale M
  have ha : IsSelfAdjoint a := .star_mul_self x
  have hf : Continuous f := continuous_clipScale hM
  let y := x * cfc f a
  have hprod : star y * y = cfc (fun t => f t * t * f t) a := by
    dsimp only [y]
    rw [star_mul, (IsSelfAdjoint.cfc (f := f) (a := a)).star_eq]
    rw [cfc_mul (fun t => f t * t) f a (hf.mul continuous_id).continuousOn hf.continuousOn,
      cfc_mul f (fun t : ℝ => t) a hf.continuousOn continuous_id.continuousOn, cfc_id' ℝ a ha]
    dsimp only [a]
    noncomm_ring
  have hyn : ‖y‖ ≤ M := by
    have hn : ‖star y * y‖ ≤ M ^ 2 := by
      rw [hprod]
      apply norm_cfc_le (sq_nonneg M)
      intro t ht
      exact clipScale_bound hM (spectrum_star_mul_self_nonneg t ht)
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg y]
  have hφa : φ a = star (φ x) * φ x := by
    dsimp only [a]
    rw [map_mul, map_star]
  have he : cfc f (φ a) = 1 := by
    have heq : cfc f (φ a) = cfc (fun _ : ℝ => (1 : ℝ)) (φ a) := by
      apply cfc_congr
      intro t ht
      apply clipScale_eq_one hM
      have ht' := spectrum.norm_le_norm_of_mem ht
      rw [hφa, CStarRing.norm_star_mul_self] at ht'
      have ht0 : 0 ≤ t := spectrum_star_mul_self_nonneg t (hφa ▸ ht)
      rw [Real.norm_eq_abs, abs_of_nonneg ht0] at ht'
      nlinarith [norm_nonneg (φ x)]
    rw [heq, cfc_const 1 (φ a) (ha.map φ), map_one]
  refine ⟨y, ?_, hyn⟩
  dsimp only [y]
  rw [map_mul, φ.map_cfc f a hf.continuousOn (ha := ha) (hφa := ha.map φ), he, mul_one]

theorem starHom_isClosed_range (φ : A →⋆ₐ[ℂ] B) : IsClosed (Set.range φ) := by
  let f : A →L[ℂ] B := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
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
      · obtain ⟨y, hy, hyn⟩ := starHom_exists_lift_norm_le φ x (norm_pos_iff.mpr hx) le_rfl
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

end Unital

end WeakPureInfiniteness
end

end OAI
