import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

include hτ in
lemma norm_star_preGNS (a : A) : ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_star]
  rw [hτ]

noncomputable def rightMulPre (a : A) : τ.PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ τ.ofPreGNS.toLinearMap).mkContinuous
    ‖a‖ (fun x => by
      change ‖τ.toPreGNS (τ.ofPreGNS x * a)‖ ≤ ‖a‖ * ‖x‖
      calc
        _ = ‖τ.toPreGNS (star (τ.ofPreGNS x * a))‖ :=
          (norm_star_preGNS τ hτ _).symm
        _ = ‖τ.leftMulMapPreGNS (star a) (τ.toPreGNS (star (τ.ofPreGNS x)))‖ := by
          simp only [star_mul, PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS_toPreGNS]
        _ ≤ ‖star a‖ * ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ := by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right
              (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) (norm_nonneg _))
        _ = ‖a‖ * ‖x‖ := by
          rw [norm_star, norm_star_preGNS τ hτ, PositiveLinearMap.toPreGNS_ofPreGNS])

@[simp] lemma rightMulPre_apply (a : A) (x : τ.PreGNS) :
    rightMulPre τ hτ a x = τ.toPreGNS (τ.ofPreGNS x * a) := rfl

lemma norm_rightMulPre_le (a : A) : ‖rightMulPre τ hτ a‖ ≤ ‖a‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

noncomputable def rightMul (a : A) : τ.GNS →L[ℂ] τ.GNS :=
  (rightMulPre τ hτ a).completion

@[simp] lemma rightMul_coe (a : A) (x : τ.PreGNS) :
    rightMul τ hτ a (x : τ.GNS) = (τ.toPreGNS (τ.ofPreGNS x * a) : τ.GNS) := by
  simp [rightMul]

lemma rightMul_mul (a b : A) :
    rightMul τ hτ (a * b) = rightMul τ hτ b * rightMul τ hτ a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_apply_eq_comp, mul_assoc]

lemma rightMul_one : rightMul τ hτ 1 = 1 := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp

lemma left_right_commute (a b : A) :
    τ.gnsStarAlgHom a * rightMul τ hτ b = rightMul τ hτ b * τ.gnsStarAlgHom a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_apply_eq_comp, PositiveLinearMap.gnsStarAlgHom,
      PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, mul_assoc]

lemma rightMul_star (a : A) : rightMul τ hτ (star a) = (rightMul τ hτ a).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightMul_coe, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_mul, star_star]
    rw [mul_assoc, hτ, mul_assoc]

noncomputable def vacuum : τ.GNS := (τ.toPreGNS 1 : τ.GNS)

lemma left_vacuum (a : A) : τ.gnsStarAlgHom a (vacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [vacuum, PositiveLinearMap.gnsStarAlgHom]

lemma right_vacuum (a : A) : rightMul τ hτ a (vacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [vacuum]

lemma vacuum_norm_sq : ‖vacuum τ‖ ^ 2 = (τ 1).re := by
  simp only [vacuum, Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]
  exact Real.sq_sqrt (τ.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

lemma vacuum_norm (h1 : τ 1 = 1) : ‖vacuum τ‖ = 1 := by
  have h := vacuum_norm_sq τ
  rw [h1] at h
  have := norm_nonneg (vacuum τ)
  change ‖vacuum τ‖ ^ 2 = 1 at h
  nlinarith

lemma dense_cyclic_orbit : DenseRange (fun a : A => τ.gnsStarAlgHom a (vacuum τ)) := by
  have hd := Completion.denseRange_coe (α := τ.PreGNS)
  have he : (fun a : A => τ.gnsStarAlgHom a (vacuum τ)) =
      (fun x : τ.PreGNS => (x : τ.GNS)) ∘ τ.toPreGNS := by
    funext a
    exact left_vacuum τ a
  rw [he]
  exact hd.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

noncomputable def rightStarAlgHom : Aᵐᵒᵖ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := rightMul τ hτ a.unop
  map_one' := rightMul_one τ hτ
  map_zero' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [mul_add, Completion.coe_add]
  map_mul' a b := rightMul_mul τ hτ b.unop a.unop
  commutes' c := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [Algebra.algebraMap_eq_smul_one, Completion.coe_smul]
  map_star' a := rightMul_star τ hτ a.unop

lemma rightMul_opNorm_le (a : A) : ‖rightMul τ hτ a‖ ≤ ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le (rightStarAlgHom τ hτ) (MulOpposite.op a)

lemma coe_preGNS_eq_zero_iff
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    (τ.toPreGNS a : τ.GNS) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hfaith a
    have hn : ‖τ.toPreGNS a‖ = 0 := by
      rw [← Completion.norm_coe, h, norm_zero]
    have := τ.preGNS_norm_sq (τ.toPreGNS a)
    simpa [hn] using this.symm
  · rintro rfl
    simp [Completion.coe_zero]

lemma left_faithful (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective τ.gnsStarAlgHom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply (coe_preGNS_eq_zero_iff τ hfaith a).mp
  rw [← left_vacuum τ a, ha, zero_apply]

lemma right_faithful (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective (rightStarAlgHom τ hτ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply MulOpposite.unop_injective
  apply (coe_preGNS_eq_zero_iff τ hfaith a.unop).mp
  rw [← right_vacuum τ hτ a.unop]
  change (rightStarAlgHom τ hτ a) (vacuum τ) = 0
  rw [ha, zero_apply]

lemma norm_left_eq (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    ‖τ.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (left_faithful τ hfaith) a

lemma norm_right_eq (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    ‖rightMul τ hτ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (right_faithful τ hτ hfaith) (MulOpposite.op a)

lemma coe_norm_sq (a : A) : ‖(τ.toPreGNS a : τ.GNS)‖ ^ 2 = (τ (star a * a)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), Completion.inner_coe]
  rfl

lemma projection_norm_sq {p : A} (hp : IsStarProjection p) :
    ‖(τ.toPreGNS p : τ.GNS)‖ ^ 2 = (τ p).re := by
  rw [coe_norm_sq, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

lemma norm_right_partial_isometry {v r : A} (hv : star v * v = r)
    {ξ : τ.GNS} (hξ : rightMul τ hτ r ξ = ξ) :
    ‖rightMul τ hτ (star v) ξ‖ = ‖ξ‖ := by
  have hcomp : (rightMul τ hτ (star v)).adjoint.comp (rightMul τ hτ (star v)) =
      rightMul τ hτ r := by
    change (rightMul τ hτ (star v)).adjoint * rightMul τ hτ (star v) = _
    rw [← rightMul_star, star_star, ← rightMul_mul, hv]
  have hs := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
    (rightMul τ hτ (star v)) ξ
  rw [hcomp, hξ, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

@[simp] lemma left_coe (a b : A) :
    τ.gnsStarAlgHom a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (a * b) : τ.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom]

lemma mem_closure_corner_orbit {e r : A} (her : e * r = r)
    {ξ : τ.GNS} (heξ : τ.gnsStarAlgHom e ξ = ξ)
    (hrξ : rightMul τ hτ r ξ = ξ) :
    ξ ∈ closure (Set.range (fun a : A =>
      τ.gnsStarAlgHom (e * a * e) (τ.toPreGNS r : τ.GNS))) := by
  let F : τ.GNS →L[ℂ] τ.GNS := (τ.gnsStarAlgHom e).comp (rightMul τ hτ r)
  have hF : F ξ = ξ := by
    change τ.gnsStarAlgHom e (rightMul τ hτ r ξ) = ξ
    rw [hrξ, heξ]
  rw [← hF]
  apply map_mem_closure F.continuous (dense_cyclic_orbit τ ξ)
  rintro x ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  change τ.gnsStarAlgHom (e * a * e) (τ.toPreGNS r : τ.GNS) =
    τ.gnsStarAlgHom e (rightMul τ hτ r (τ.gnsStarAlgHom a (vacuum τ)))
  simp only [left_vacuum, rightMul_coe, PositiveLinearMap.ofPreGNS_toPreGNS,
    left_coe, mul_assoc, her]

end TracialGNS

end Kadison
end

end OAI
