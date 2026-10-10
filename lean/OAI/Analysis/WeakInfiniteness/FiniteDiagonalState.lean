import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

lemma tensor_inner_smul_smul {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y : E ⊗[ℂ] K) (c : ℂ) :
    inner ℂ (c • x) (c • y) = star c * c * inner ℂ x y := by
  calc
    _ = star c * inner ℂ x (c • y) := inner_smul_left x (c • y) c
    _ = star c * (c * inner ℂ x y) := congrArg (star c * ·) (inner_smul_right x y c)
    _ = _ := by ring

variable (F : Type*) [Group F] [Fintype F] [DecidableEq F]

noncomputable def finiteLeftRegularIsometry :
    F →* (EuclideanSpace ℂ F ≃ₗᵢ[ℂ] EuclideanSpace ℂ F) where
  toFun s := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft s)
  map_one' := by
    ext ξ g
    change ξ ((1 : F)⁻¹ * g) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ ((s * t)⁻¹ * g) = ξ (t⁻¹ * (s⁻¹ * g))
    simp [mul_assoc]

noncomputable def finiteLeftRegular : F →* unitary (EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (finiteLeftRegularIsometry F)

omit [DecidableEq F] in
@[simp]

lemma finiteLeftRegular_apply (s : F) (ξ : EuclideanSpace ℂ F) (g : F) :
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F) ξ g = ξ (s⁻¹ * g) := rfl

@[simp]
lemma finiteLeftRegular_single (s g : F) :
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
      (EuclideanSpace.single g (1 : ℂ)) = EuclideanSpace.single (s * g) (1 : ℂ) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft_single (Equiv.mulLeft s) g 1

noncomputable def finiteDiagonalVector :
    EuclideanSpace ℂ F ⊗[ℂ] EuclideanSpace ℂ F :=
  ∑ g : F, EuclideanSpace.single g (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single g (1 : ℂ)

lemma inner_finiteDiagonalVector_translate (s t : F) :
    inner ℂ (finiteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteDiagonalVector F)) = if s = t then (Fintype.card F : ℂ) else 0 := by
  classical
  simp only [finiteDiagonalVector, map_sum, TensorProduct.mapL_tmul,
    finiteLeftRegular_single, inner_sum, sum_inner, TensorProduct.inner_tmul,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst]
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.sum_eq_zero
    intro h _
    by_cases hg : h = s * g
    · simp [hg, hst]
    · simp [hg]

lemma inner_finiteDiagonalVector_self :
    inner ℂ (finiteDiagonalVector F) (finiteDiagonalVector F) = (Fintype.card F : ℂ) := by
  have h := inner_finiteDiagonalVector_translate F 1 1
  simpa using h

noncomputable def normalizedFiniteDiagonalVector :
    EuclideanSpace ℂ F ⊗[ℂ] EuclideanSpace ℂ F :=
  ((Real.sqrt (Fintype.card F : ℝ))⁻¹ : ℂ) • finiteDiagonalVector F

lemma normalizedFiniteDiagonalVector_inner_translate (s t : F) :
    inner ℂ (normalizedFiniteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (normalizedFiniteDiagonalVector F)) = if s = t then 1 else 0 := by
  classical
  have hc : (Fintype.card F : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hsq : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hc.le
  let c : ℂ := (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹
  let T := TensorProduct.mapL
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
    (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
  have hi := tensor_inner_smul_smul (finiteDiagonalVector F) (T (finiteDiagonalVector F)) c
  have ht := inner_finiteDiagonalVector_translate F s t
  change inner ℂ (c • finiteDiagonalVector F) (T (c • finiteDiagonalVector F)) = _
  rw [map_smul]
  calc
    _ = star c * c * inner ℂ (finiteDiagonalVector F) (T (finiteDiagonalVector F)) := hi
    _ = star c * c * (if s = t then (Fintype.card F : ℂ) else 0) :=
      congrArg (star c * c * ·) ht
    _ = _ := by
      simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
      by_cases hst : s = t
      · simp only [ite_eq_left hst]
        rw [← hsq]
        have hsc : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
        field_simp
      · simp [hst]

lemma norm_normalizedFiniteDiagonalVector : ‖normalizedFiniteDiagonalVector F‖ = 1 := by
  have h : inner ℂ (normalizedFiniteDiagonalVector F) (normalizedFiniteDiagonalVector F) = 1 := by
    simpa using normalizedFiniteDiagonalVector_inner_translate F 1 1
  calc
    _ = Real.sqrt (Complex.re (inner ℂ (normalizedFiniteDiagonalVector F)
      (normalizedFiniteDiagonalVector F))) :=
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (normalizedFiniteDiagonalVector F)
    _ = 1 := by rw [h]; simp

end WeakPureInfiniteness
end

end OAI
