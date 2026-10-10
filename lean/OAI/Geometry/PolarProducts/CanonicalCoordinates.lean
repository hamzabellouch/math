import OAI.Geometry.PolarProducts.PlanarSquare

namespace OAI

universe u131 u132 u133

section
namespace CanonicalLinear
noncomputable section
open scoped InnerProductSpace
variable {κ : Type u131} [Fintype κ] [DecidableEq κ]
abbrev E (κ : Type u132) := EuclideanSpace ℝ κ

def coordinate (j : κ) : E κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : κ => ℝ) j

def adaptedMap (u v : E κ) (j : κ) : E κ →L[ℝ] E κ :=
  ContinuousLinearMap.id ℝ (E κ) - (1 / u j) • (coordinate j).smulRight u +
    (innerSL ℝ v).smulRight (EuclideanSpace.single j 1)

@[simp] theorem adaptedMap_apply (u v q : E κ) (j : κ) :
    adaptedMap u v j q = q - (q j / u j) • u + (inner (𝕜 := ℝ) v q) • EuclideanSpace.single j 1 := by
  simp [adaptedMap, coordinate, div_eq_mul_inv, smul_smul, mul_comm]

theorem adaptedMap_coordinate (u v q : E κ) (j : κ) (huj : u j ≠ 0) :
    adaptedMap u v j q j = inner (𝕜 := ℝ) v q := by
  simp [adaptedMap_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, div_mul_cancel₀ _ huj]

theorem adaptedMap_u {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : adaptedMap u v j u = EuclideanSpace.single j 1 := by
  simp [adaptedMap_apply, div_self huj, hvu]

theorem adaptedMap_injective {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : Function.Injective (adaptedMap u v j) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro q hq
  change adaptedMap u v j q = 0 at hq
  have hi : inner (𝕜 := ℝ) v q = 0 := by
    have hh := congrArg (fun x : E κ => x j) hq
    simpa only [adaptedMap_coordinate u v q j huj, PiLp.zero_apply] using hh
  have he : q = (q j/u j) • u := by
    simpa only [adaptedMap_apply, hi, zero_smul, add_zero, sub_eq_zero] using hq
  have ht : q j/u j = 0 := by
    have hh := congrArg (fun x : E κ => inner (𝕜 := ℝ) v x) he
    simpa only [real_inner_smul_right, hvu, mul_one, hi] using hh.symm
  simp only [ht, zero_smul] at he
  exact he

def adapted {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : E κ ≃L[ℝ] E κ :=
  ContinuousLinearEquiv.ofBijective (adaptedMap u v j)
    (LinearMap.ker_eq_bot.mpr (adaptedMap_injective j huj hvu))
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective (adaptedMap_injective j huj hvu)))

@[simp] theorem adapted_apply {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (q : E κ) :
    adapted j huj hvu q = adaptedMap u v j q := rfl

theorem adapted_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (q : E κ) :
    adapted j huj hvu q j = inner (𝕜 := ℝ) v q := adaptedMap_coordinate u v q j huj

theorem adapted_inverse_single {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) :
    (adapted j huj hvu).symm (EuclideanSpace.single j 1) = u := by
  apply (adapted j huj hvu).injective
  simpa only [ContinuousLinearEquiv.apply_symm_apply, adapted_apply] using (adaptedMap_u j huj hvu).symm

def cotangent (A : E κ ≃L[ℝ] E κ) : (E κ × E κ) →L[ℝ] (E κ × E κ) :=
  (A.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ (E κ) (E κ))).prod
    (A.symm.toContinuousLinearMap.adjoint.comp (ContinuousLinearMap.snd ℝ (E κ) (E κ)))

omit [DecidableEq κ] in
@[simp] theorem cotangent_apply (A : E κ ≃L[ℝ] E κ) (x : E κ × E κ) :
    cotangent A x = (A x.1, A.symm.toContinuousLinearMap.adjoint x.2) := rfl

omit [DecidableEq κ] in
theorem cotangent_preserves (A : E κ ≃L[ℝ] E κ) (x y : E κ × E κ) :
    inner (𝕜 := ℝ) (cotangent A x).1 (cotangent A y).2 -
      inner (𝕜 := ℝ) (cotangent A y).1 (cotangent A x).2 =
    inner (𝕜 := ℝ) x.1 y.2 - inner (𝕜 := ℝ) y.1 x.2 := by
  simp only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

omit [DecidableEq κ] in
theorem cotangent_injective (A : E κ ≃L[ℝ] E κ) : Function.Injective (cotangent A) := by
  intro x y hxy
  apply Prod.ext
  · exact A.injective (congrArg Prod.fst hxy)
  · apply ext_inner_left ℝ
    intro z
    obtain ⟨w,rfl⟩ := A.symm.surjective z
    have hh := congrArg (fun t : E κ × E κ => inner (𝕜 := ℝ) w t.2) hxy
    simpa only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearEquiv.coe_coe] using hh

theorem cotangent_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (x : E κ × E κ) :
    (cotangent (adapted j huj hvu) x).1 j = inner (𝕜 := ℝ) v x.1 ∧
    (cotangent (adapted j huj hvu) x).2 j = inner (𝕜 := ℝ) u x.2 := by
  constructor
  · exact adapted_first j huj hvu x.1
  · calc
      _ = inner (𝕜 := ℝ) (EuclideanSpace.single j 1) (cotangent (adapted j huj hvu) x).2 := by simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
      _ = _ := by
        simp only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
          ContinuousLinearEquiv.coe_coe, adapted_inverse_single]

end
end CanonicalLinear
end

section
namespace UpperCoordinates
noncomputable section
open Set
open scoped ContDiff
variable {κ : Type u133} [Fintype κ] [DecidableEq κ]
open ComplexCoordinates CanonicalLinear

def phaseForm (x y : R κ × R κ) : ℝ :=
  inner (𝕜 := ℝ) x.1 y.2 - inner (𝕜 := ℝ) y.1 x.2

omit [DecidableEq κ] in
theorem form_parts (v w : C κ) : PlanarCylinder.form v w = phaseForm (parts v) (parts w) := by
  simp only [PlanarCylinder.form, PlanarSquare.form, phaseForm, parts_apply, PiLp.inner_apply,
    re_apply, im_apply, RCLike.inner_apply', RCLike.conj_to_real, ← Finset.sum_sub_distrib]

omit [DecidableEq κ] in
theorem form_parts_symm (x y : R κ × R κ) :
    PlanarCylinder.form (parts.symm x) (parts.symm y) = phaseForm x y := by
  rw [form_parts, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

def targetCoordinates (A : E κ ≃L[ℝ] E κ) : (E κ × E κ) →L[ℝ] C κ :=
  parts.symm.toContinuousLinearMap.comp (cotangent A)

omit [DecidableEq κ] in
theorem targetCoordinates_preserves (A : E κ ≃L[ℝ] E κ) (x y : E κ × E κ) :
    PlanarCylinder.form (targetCoordinates A x) (targetCoordinates A y) = phaseForm x y := by
  change PlanarCylinder.form (parts.symm (cotangent A x)) (parts.symm (cotangent A y)) = _
  rw [form_parts_symm]
  exact cotangent_preserves A x y

omit [DecidableEq κ] in
theorem targetCoordinates_injective (A : E κ ≃L[ℝ] E κ) :
    Function.Injective (targetCoordinates A) :=
  parts.symm.injective.comp (cotangent_injective A)

theorem targetCoordinates_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (x : E κ × E κ) :
    (targetCoordinates (adapted j huj hvu) x j).re = inner (𝕜 := ℝ) v x.1 ∧
    (targetCoordinates (adapted j huj hvu) x j).im = inner (𝕜 := ℝ) u x.2 := by
  have hh := cotangent_first j huj hvu x
  have hp := parts.apply_symm_apply (cotangent (adapted j huj hvu) x)
  have hre : re (parts.symm (cotangent (adapted j huj hvu) x)) = (cotangent (adapted j huj hvu) x).1 :=
    congrArg Prod.fst hp
  have him : im (parts.symm (cotangent (adapted j huj hvu) x)) = (cotangent (adapted j huj hvu) x).2 :=
    congrArg Prod.snd hp
  change re (parts.symm (cotangent (adapted j huj hvu) x)) j = _ ∧
    im (parts.symm (cotangent (adapted j huj hvu) x)) j = _
  rw [hre, him]
  exact hh

end
end UpperCoordinates
end

end OAI
