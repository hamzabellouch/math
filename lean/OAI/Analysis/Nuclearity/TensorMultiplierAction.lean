import OAI.Analysis.PureInfiniteness.MultiplierIntertwining
import OAI.Analysis.WeakInfiniteness.TensorMultiplier

namespace OAI

/-! # The unital right factor acts on a nonunital minimal tensor product -/

noncomputable section
open scoped MultiplierAlgebra

namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {D : Type v} [NonUnitalCStarAlgebra A] [CStarAlgebra D]

private lemma spatialRight_zero : spatialRightMultiplier (A := A) (0 : D) = 0 :=
  map_zero (spatialRightMultiplierHom (A := A))

private lemma spatialRight_add (d e : D) :
    spatialRightMultiplier (A := A) (d + e) = spatialRightMultiplier d + spatialRightMultiplier e :=
  map_add (spatialRightMultiplierHom (A := A)) d e

private lemma spatialRight_mul (d e : D) :
    spatialRightMultiplier (A := A) (d * e) = spatialRightMultiplier d * spatialRightMultiplier e :=
  map_mul (spatialRightMultiplierHom (A := A)) d e

private lemma spatialRight_smul (c : ℂ) (d : D) :
    spatialRightMultiplier (A := A) (c • d) = c • spatialRightMultiplier d :=
  map_smul (spatialRightMultiplierHom (A := A)) c d

private lemma spatialRight_star (d : D) :
    spatialRightMultiplier (A := A) (star d) = star (spatialRightMultiplier d) :=
  map_star (spatialRightMultiplierHom (A := A)) d

def tensorRightAction (d : D) : MinimalTensor A D →L[ℂ] MinimalTensor A D :=
  LinearMap.mkContinuous
    { toFun := tensorRightMultiply d
      map_add' := fun x y => Subtype.ext (add_mul x.val y.val _)
      map_smul' := fun c x => Subtype.ext (smul_mul_assoc c x.val _) }
    ‖d‖ (fun x => by
      change ‖x.val * spatialRightMultiplier d‖ ≤ ‖d‖ * ‖x.val‖
      have hm := NonUnitalStarAlgHom.norm_apply_le (spatialRightMultiplierHom (A := A)) d
      change ‖spatialRightMultiplier (A := A) d‖ ≤ ‖d‖ at hm
      exact (norm_mul_le _ _).trans
        ((mul_le_mul_of_nonneg_left hm (norm_nonneg x.val)).trans_eq (mul_comm _ _)))

def tensorLeftAction (d : D) : MinimalTensor A D →L[ℂ] MinimalTensor A D :=
  LinearMap.mkContinuous
    { toFun := fun x => star (tensorRightAction (star d) (star x))
      map_add' := by intro x y; simp only [star_add, map_add]
      map_smul' := by intro c x; simp only [star_smul, map_smul, star_star, RingHom.id_apply] }
    ‖d‖ (fun x => by
      change ‖star (tensorRightAction (star d) (star x))‖ ≤ ‖d‖ * ‖x‖
      rw [norm_star]
      have hr : ‖tensorRightAction (A := A) (star d)‖ ≤ ‖star d‖ :=
        LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
      exact ((tensorRightAction (A := A) (star d)).le_opNorm (star x)).trans
        (by simpa only [norm_star] using
          mul_le_mul_of_nonneg_right hr (norm_nonneg (star x))))

@[simp] lemma tensorRightAction_val (d : D) (x : MinimalTensor A D) :
    (tensorRightAction d x).val = x.val * spatialRightMultiplier d := rfl

@[simp] lemma tensorLeftAction_val (d : D) (x : MinimalTensor A D) :
    (tensorLeftAction d x).val = spatialRightMultiplier d * x.val := by
  change star ((star x.val) * spatialRightMultiplier (star d)) = _
  rw [spatialRight_star, star_mul, star_star, star_star]

@[simp] lemma tensorRightAction_elementary (d e : D) (a : A) :
    tensorRightAction d (minimalElementary a e) = minimalElementary a (e * d) :=
  Subtype.ext (spatialElementary_mul_rightMultiplier a e d)

@[simp] lemma tensorLeftAction_elementary (d e : D) (a : A) :
    tensorLeftAction d (minimalElementary a e) = minimalElementary a (d * e) := by
  change star (tensorRightAction (star d) (star (minimalElementary a e))) = _
  rw [← minimalElementary_star, tensorRightAction_elementary, ← minimalElementary_star]
  simp only [star_star, star_mul]

lemma tensorRightAction_one (x : MinimalTensor A D) : tensorRightAction (1 : D) x = x := by
  apply minimalPolynomial_denseRange.induction_on
    (p := fun x => tensorRightAction (1 : D) x = x) x
    (isClosed_eq (tensorRightAction (A := A) (1 : D)).continuous continuous_id)
  intro c
  simp only [minimalPolynomial, Finsupp.sum, map_sum, map_smul,
    tensorRightAction_elementary, mul_one]

lemma tensorLeftAction_one (x : MinimalTensor A D) : tensorLeftAction (1 : D) x = x := by
  change star (tensorRightAction (star (1 : D)) (star x)) = x
  rw [star_one, tensorRightAction_one, star_star]

def tensorRightFactorMultiplier (d : D) : 𝓜(ℂ, MinimalTensor A D) where
  fst := tensorLeftAction d
  snd := tensorRightAction d
  central := by
    intro x y
    apply Subtype.ext
    change (tensorRightAction d x).val * y.val = x.val * (tensorLeftAction d y).val
    rw [tensorRightAction_val, tensorLeftAction_val, mul_assoc]

def tensorRightFactorHom : D →⋆ₐ[ℂ] 𝓜(ℂ, MinimalTensor A D) where
  toFun := tensorRightFactorMultiplier
  map_zero' := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x <;> apply Subtype.ext
    · change (tensorLeftAction (0 : D) x).val = 0
      rw [tensorLeftAction_val, spatialRight_zero, zero_mul]
    · change (tensorRightAction (0 : D) x).val = 0
      rw [tensorRightAction_val, spatialRight_zero, mul_zero]
  map_add' d e := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x <;> apply Subtype.ext
    · change (tensorLeftAction (d + e) x).val =
        (tensorLeftAction d x).val + (tensorLeftAction e x).val
      simp only [tensorLeftAction_val, spatialRight_add, add_mul]
    · change (tensorRightAction (d + e) x).val =
        (tensorRightAction d x).val + (tensorRightAction e x).val
      simp only [tensorRightAction_val, spatialRight_add, mul_add]
  map_mul' d e := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x <;> apply Subtype.ext
    · change (tensorLeftAction (d * e) x).val =
        (tensorLeftAction d (tensorLeftAction e x)).val
      simp only [tensorLeftAction_val, spatialRight_mul, mul_assoc]
    · change (tensorRightAction (d * e) x).val =
        (tensorRightAction e (tensorRightAction d x)).val
      simp only [tensorRightAction_val, spatialRight_mul, mul_assoc]
  map_one' := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
    · exact tensorLeftAction_one x
    · exact tensorRightAction_one x
  commutes' c := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x <;> apply Subtype.ext
    · change (tensorLeftAction (algebraMap ℂ D c) x).val = c • x.val
      rw [Algebra.algebraMap_eq_smul_one, tensorLeftAction_val,
        spatialRight_smul, smul_mul_assoc]
      have h := congrArg Subtype.val (tensorLeftAction_one x)
      rw [tensorLeftAction_val] at h
      rw [h]
    · change (tensorRightAction (algebraMap ℂ D c) x).val = c • x.val
      rw [Algebra.algebraMap_eq_smul_one, tensorRightAction_val,
        spatialRight_smul, mul_smul_comm]
      have h := congrArg Subtype.val (tensorRightAction_one x)
      rw [tensorRightAction_val] at h
      rw [h]
  map_star' d := by
    apply DoubleCentralizer.ext
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
    · change tensorLeftAction (star d) x = star (tensorRightAction d (star x))
      change star (tensorRightAction (star (star d)) (star x)) = _
      rw [star_star]
    · change tensorRightAction (star d) x = star (tensorLeftAction d (star x))
      change tensorRightAction (star d) x = star (star (tensorRightAction (star d) (star (star x))))
      rw [star_star, star_star]

lemma coe_mul_tensorRightFactor (x : MinimalTensor A D) (d : D) :
    DoubleCentralizer.coeHom x * tensorRightFactorHom d =
      DoubleCentralizer.coeHom (tensorRightAction d x) := by
  apply DoubleCentralizer.ext
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro y <;> apply Subtype.ext
  · change x.val * (tensorLeftAction d y).val = (tensorRightAction d x).val * y.val
    rw [tensorLeftAction_val, tensorRightAction_val, mul_assoc]
  · change (tensorRightAction d (y * x)).val = y.val * (tensorRightAction d x).val
    rw [tensorRightAction_val, tensorRightAction_val]
    exact mul_assoc _ _ _

lemma tensorRightFactor_mul_coe (x : MinimalTensor A D) (d : D) :
    tensorRightFactorHom d * DoubleCentralizer.coeHom x =
      DoubleCentralizer.coeHom (tensorLeftAction d x) := by
  apply DoubleCentralizer.ext
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro y <;> apply Subtype.ext
  · change (tensorLeftAction d (x * y)).val = (tensorLeftAction d x).val * y.val
    rw [tensorLeftAction_val, tensorLeftAction_val]
    exact (mul_assoc _ _ _).symm
  · change (tensorRightAction d y).val * x.val = y.val * (tensorLeftAction d x).val
    rw [tensorRightAction_val, tensorLeftAction_val, mul_assoc]

lemma tensorMultiplier_coefficient (a : A) (d : D) :
    DoubleCentralizer.coeHom (minimalLeftEmbedding A D a) * tensorRightFactorHom d =
      DoubleCentralizer.coeHom (minimalElementary a d) := by
  rw [coe_mul_tensorRightFactor]
  change DoubleCentralizer.coeHom (tensorRightAction d (minimalElementary a 1)) = _
  rw [tensorRightAction_elementary, one_mul]

lemma tensorMultiplier_commute (a : A) (d : D) :
    Commute (DoubleCentralizer.coeHom (minimalLeftEmbedding A D a))
      (tensorRightFactorHom d) := by
  change _ = _
  rw [tensorMultiplier_coefficient, tensorRightFactor_mul_coe]
  change _ = DoubleCentralizer.coeHom (tensorLeftAction d (minimalElementary a 1))
  rw [tensorLeftAction_elementary, mul_one]

end WeakPureInfiniteness

end

end OAI
