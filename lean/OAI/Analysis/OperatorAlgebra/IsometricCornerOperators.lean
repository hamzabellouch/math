import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression

namespace OAI

/-! Inclusion and compression of a closed Hilbert subspace transfer an
expectation to represented projection corners. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev isometricCornerCompress (V : K →ₗᵢ[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K) :=
  hilbertCompression (StarAlgHom.id ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
    V.toContinuousLinearMap

def isometricCornerLift (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) : H →L[ℂ] H :=
  V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)

abbrev isometricCornerProjection (V : K →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

lemma isometricCorner_adjoint_apply (V : K →ₗᵢ[ℂ] H) (x : K) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  exact congrArg (fun T : K →L[ℂ] K => T x) V.adjoint_comp_self

@[simp] lemma isometricCornerCompress_apply (V : K →ₗᵢ[ℂ] H)
    (T : H →L[ℂ] H) (x : K) :
    isometricCornerCompress V T x = V.toContinuousLinearMap.adjoint (T (V x)) := rfl

@[simp] lemma isometricCornerLift_apply (V : K →ₗᵢ[ℂ] H)
    (T : K →L[ℂ] K) (x : H) :
    isometricCornerLift V T x = V (T (V.toContinuousLinearMap.adjoint x)) := rfl

@[simp] lemma isometricCornerCompress_lift (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) :
    isometricCornerCompress V (isometricCornerLift V T) = T := by
  ext x
  simp only [isometricCornerCompress_apply, isometricCornerLift_apply,
    isometricCorner_adjoint_apply]

lemma isometricCornerLift_injective (V : K →ₗᵢ[ℂ] H) :
    Function.Injective (isometricCornerLift V) := by
  intro T U h
  have he := congrArg (isometricCornerCompress V) h
  simpa only [isometricCornerCompress_lift] using he

lemma isometricCornerLift_mul (V : K →ₗᵢ[ℂ] H) (T U : K →L[ℂ] K) :
    isometricCornerLift V (T * U) = isometricCornerLift V T * isometricCornerLift V U := by
  ext x
  simp only [isometricCornerLift_apply, mul_apply_eq_comp,
    isometricCorner_adjoint_apply]

lemma isometricCornerLift_star (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) :
    isometricCornerLift V (star T) = star (isometricCornerLift V T) := by
  change V.toContinuousLinearMap.comp (T.adjoint.comp V.toContinuousLinearMap.adjoint) =
    (V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)).adjoint
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

def isometricCornerLiftHom (V : K →ₗᵢ[ℂ] H) :
    (K →L[ℂ] K) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := isometricCornerLift V
  map_zero' := by ext x; simp
  map_add' T U := by ext x; simp
  map_smul' c T := by ext x; simp
  map_mul' := isometricCornerLift_mul V
  map_star' := isometricCornerLift_star V

lemma isometricCornerProjection_apply (V : K →ₗᵢ[ℂ] H) (x : H) :
    isometricCornerProjection V x = V (V.toContinuousLinearMap.adjoint x) := rfl

@[simp] lemma isometricCornerProjection_inclusion (V : K →ₗᵢ[ℂ] H) (x : K) :
    isometricCornerProjection V (V x) = V x := by
  rw [isometricCornerProjection_apply, isometricCorner_adjoint_apply]

lemma isometricCornerProjection_isStarProjection (V : K →ₗᵢ[ℂ] H) :
    IsStarProjection (isometricCornerProjection V) where
  isSelfAdjoint := by
    change (V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  isIdempotentElem := by
    ext x
    exact isometricCornerProjection_inclusion V _

lemma isometricCornerLift_compress (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    isometricCornerLift V (isometricCornerCompress V T) =
      isometricCornerProjection V * T * isometricCornerProjection V := by
  ext x
  rfl

lemma isometricCornerCompress_cp (V : K →ₗᵢ[ℂ] H) :
    CompletelyPositive (isometricCornerCompress V) :=
  hilbertCompression_cp _ _

lemma isometricCorner_inclusion_intertwines (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : Commute T (isometricCornerProjection V)) (x : K) :
    T (V x) = V (isometricCornerCompress V T x) := by
  have he := congrArg (fun R : H →L[ℂ] H => R (V x)) hT.eq
  simpa only [mul_apply_eq_comp, isometricCornerProjection_inclusion,
    isometricCornerProjection_apply, isometricCornerCompress_apply,
    isometricCorner_adjoint_apply] using he

lemma isometricCorner_adjoint_intertwines (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : Commute T (isometricCornerProjection V)) (x : H) :
    isometricCornerCompress V T (V.toContinuousLinearMap.adjoint x) =
      V.toContinuousLinearMap.adjoint (T x) := by
  have he := congrArg (fun R : H →L[ℂ] H => R x) hT.eq
  change T (isometricCornerProjection V x) = isometricCornerProjection V (T x) at he
  change V.toContinuousLinearMap.adjoint (T (isometricCornerProjection V x)) = _
  rw [he, isometricCornerProjection_apply, isometricCorner_adjoint_apply]

lemma isometricCornerLift_mul_right (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K)
    (b : H →L[ℂ] H) (hb : Commute b (isometricCornerProjection V)) :
    isometricCornerLift V T * b = isometricCornerLift V (T * isometricCornerCompress V b) := by
  ext x
  simp only [mul_apply_eq_comp, isometricCornerLift_apply]
  rw [isometricCorner_adjoint_intertwines V b hb]

lemma isometricCornerLift_mul_left (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K)
    (b : H →L[ℂ] H) (hb : Commute b (isometricCornerProjection V)) :
    b * isometricCornerLift V T = isometricCornerLift V (isometricCornerCompress V b * T) := by
  ext x
  simp only [mul_apply_eq_comp, isometricCornerLift_apply]
  exact isometricCorner_inclusion_intertwines V b hb _

lemma isometricCornerLift_commute_iff (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K)
    (b : H →L[ℂ] H) (hb : Commute b (isometricCornerProjection V)) :
    Commute (isometricCornerLift V T) b ↔ Commute T (isometricCornerCompress V b) := by
  simp only [Commute, SemiconjBy, isometricCornerLift_mul_right V T b hb,
    isometricCornerLift_mul_left V T b hb, (isometricCornerLift_injective V).eq_iff]

lemma isometricCornerCompress_norm_le (V : K →ₗᵢ[ℂ] H) :
    ‖isometricCornerCompress V‖ ≤ 1 := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  exact (hilbertCompression_norm_le _ _).trans
    ((mul_le_mul hv hv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

variable {A : Type*} [CStarAlgebra A]

def isometricCornerRestrictHom (V : K →ₗᵢ[ℂ] H)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : ∀ a, Commute (π a) (isometricCornerProjection V)) :
    A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := isometricCornerCompress V (π a)
  map_zero' := by simp
  map_one' := by ext x; simp [isometricCorner_adjoint_apply]
  map_add' a b := by simp
  map_mul' a b := by
    ext x
    simp only [map_mul, isometricCornerCompress_apply, mul_apply_eq_comp]
    exact congrArg (fun y : H => V.toContinuousLinearMap.adjoint (π a y))
      (isometricCorner_inclusion_intertwines V (π b) (hπ b) x)
  commutes' c := by
    ext x
    change V.toContinuousLinearMap.adjoint (π ((algebraMap ℂ A) c) (V x)) = _
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, smul_apply,
      one_apply_eq_self, isometricCorner_adjoint_apply]
  map_star' a := by
    change V.toContinuousLinearMap.adjoint.comp
      ((π (star a)).comp V.toContinuousLinearMap) =
      (V.toContinuousLinearMap.adjoint.comp ((π a).comp V.toContinuousLinearMap)).adjoint
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

end WeakPureInfiniteness

end

end OAI
