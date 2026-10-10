import OAI.Analysis.BoundedHochschild.AdditivePositiveSupport

namespace OAI

/-! Normality of positive functionals localized to a projection corner. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Two-sided compression of a positive functional. -/
def compressionPositive {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) : M →ₚ[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun a => ψ (p * a * p)
      map_add' := by intro a b; simp only [mul_add, add_mul, map_add]
      map_smul' := by intro c a; simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
  monotone' := fun _ _ hab => ψ.monotone (by
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_le_conjugate hab p)

lemma compressionPositive_clm {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (compressionPositive hp ψ) =
      ((positiveFunctionalCLM ψ).comp ((ContinuousLinearMap.mul ℂ M).flip p)).comp
        (ContinuousLinearMap.mul ℂ M p) := rfl

@[simp] lemma compressionPositive_one {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) :
    compressionPositive hp ψ 1 = ψ p := by
  change ψ (p * 1 * p) = ψ p
  rw [mul_one, hp.isIdempotentElem.eq]

lemma compressionPositive_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    TraceInPredual e (compressionPositive hp ψ) := by
  apply (mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mp
  rw [compressionPositive_clm]
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e p)
  exact normalDual_comp e ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) _
    ((HochschildSakai.abstract_multiplication_normal e).2 p)

/-- A singular positive functional has zero mass on every corner where its
compression is normal. -/
theorem singular_zero_of_normal_compression (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ)
    (hs : scalarNormalPart e (positiveFunctionalCLM ψ) = 0)
    (hn : TraceInPredual e (compressionPositive hp ψ)) : ψ p = 0 := by
  have hfix := scalarNormalPart_fixes e ((mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mpr hn)
  rw [compressionPositive_clm, scalarNormalPart_comp_left, scalarNormalPart_comp_right, hs] at hfix
  have hc : positiveFunctionalCLM (compressionPositive hp ψ) = 0 := by
    rw [compressionPositive_clm]
    simpa only [ContinuousLinearMap.zero_comp] using hfix.symm
  have he := congrArg (fun F : StrongDual ℂ M => F 1) hc
  change ψ (p * 1 * p) = 0 at he
  simpa only [mul_one, hp.isIdempotentElem.eq] using he

/-- Domination on the projections of a corner suffices to make a positive
compression normal when the dominating functional is normal. -/
theorem compression_normal_of_projection_dominance (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ ψ q) :
    TraceInPredual e (compressionPositive hp χ) := by
  let L := CentralCorner.includeMap p hp
  let F := (positiveFunctionalCLM ψ - positiveFunctionalCLM χ).comp L
  have hreal : ∀ a : Corner p hp, IsSelfAdjoint a → (F a).im = 0 := by
    intro a ha
    have haM : IsSelfAdjoint (a : M) := congrArg Subtype.val ha.star_eq
    have hψa : (ψ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map ψ)
    have hχa : (χ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map χ)
    change (ψ (a : M) - χ (a : M)).im = 0
    rw [Complex.sub_im, hψa, hχa, sub_self]
  have hproj : ∀ q : Corner p hp, IsStarProjection q → 0 ≤ F q := by
    intro q hq
    change 0 ≤ ψ (q : M) - χ (q : M)
    exact sub_nonneg.mpr (hle q (corner_projection_coe p hp hq) (corner_projection_le p hp hq))
  apply positive_normal_of_dominated e (compressionPositive hp χ) (compressionPositive hp ψ)
    (compressionPositive_normal e hp ψ hψ)
  intro a ha
  let c : Corner p hp := ⟨p * a * p, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq]
    · rw [mul_assoc, hp.isIdempotentElem.eq]⟩
  have hc : 0 ≤ c := by
    change 0 ≤ p * a * p
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_nonneg ha p
  have hh := eval_nonneg_of_projection_nonneg (cornerPredualEquiv p hp e) F hreal hproj c hc
  exact sub_nonneg.mp hh

end KadisonRingrose
end BoundedHochschild

end

end OAI
