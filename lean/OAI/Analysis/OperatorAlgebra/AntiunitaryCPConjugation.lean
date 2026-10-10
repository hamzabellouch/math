import OAI.Analysis.ModularRecovery.TomitaResolvent
import OAI.Analysis.Nuclearity.CPWeakOperatorUltralimit

namespace OAI

/-! Conjugating an operator-valued completely positive map on both sides
by an involutive antiunitary preserves complete positivity. This is the
operator calculation needed to transfer a commutant expectation across
Tomita conjugation. -/

noncomputable section
open scoped InnerProductSpace CStarAlgebra ComplexOrder ComplexConjugate

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def antiunitaryConjugate (J : H ≃ₗᵢ⋆[ℂ] H) (T : H →L[ℂ] H) : H →L[ℂ] H where
  toFun x := J (T (J x))
  map_add' _ _ := by simp only [map_add]
  map_smul' c x := by
    simp only [map_smulₛₗ, starRingEnd_self_apply, RingHom.id_apply]
  cont := J.continuous.comp (T.continuous.comp J.continuous)

omit [CompleteSpace H] in
@[simp] lemma antiunitaryConjugate_apply (J : H ≃ₗᵢ⋆[ℂ] H) (T : H →L[ℂ] H) (x : H) :
    antiunitaryConjugate J T x = J (T (J x)) := rfl

omit [CompleteSpace H] in
@[simp] lemma antiunitaryConjugate_add (J : H ≃ₗᵢ⋆[ℂ] H) (T U : H →L[ℂ] H) :
    antiunitaryConjugate J (T + U) = antiunitaryConjugate J T + antiunitaryConjugate J U := by
  ext x
  simp only [antiunitaryConjugate_apply, add_apply, map_add]

omit [CompleteSpace H] in
@[simp] lemma antiunitaryConjugate_smul (J : H ≃ₗᵢ⋆[ℂ] H) (c : ℂ) (T : H →L[ℂ] H) :
    antiunitaryConjugate J (c • T) = star c • antiunitaryConjugate J T := by
  ext x
  simp only [antiunitaryConjugate_apply, smul_apply,
    map_smulₛₗ, starRingEnd_apply]

omit [CompleteSpace H] in
lemma antiunitaryConjugate_involutive (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (T : H →L[ℂ] H) : antiunitaryConjugate J (antiunitaryConjugate J T) = T := by
  ext x
  simp only [antiunitaryConjugate_apply]
  rw [hJ x, hJ (T x)]

omit [CompleteSpace H] in
lemma antiunitaryConjugate_norm_le (J : H ≃ₗᵢ⋆[ℂ] H) (T : H →L[ℂ] H) :
    ‖antiunitaryConjugate J T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  simpa only [antiunitaryConjugate_apply, J.norm_map] using T.le_opNorm (J x)

def antiunitaryMatrix (J : H ≃ₗᵢ⋆[ℂ] H) {n : Type*}
    (X : CStarMatrix n n (H →L[ℂ] H)) : CStarMatrix n n (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix (fun i j => antiunitaryConjugate J (X i j))

lemma antiunitaryMatrix_nonneg (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {n : Type*} [Fintype n] (X : CStarMatrix n n (H →L[ℂ] H)) (hX : 0 ≤ X) :
    0 ≤ antiunitaryMatrix J X := by
  apply (NonUnitalStarAlgHom.map_le_map_iff
    (matrixOperatorHom (n := n) (H := H)) matrixOperator_injective).mp
  rw [map_zero]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  let y : PiLp 2 (fun _ : n => H) := WithLp.toLp 2 (fun i => J (x i))
  have he : inner ℂ (matrixOperator (antiunitaryMatrix J X) x) x =
      star (inner ℂ (matrixOperator X y) y) := by
    simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, star_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change inner ℂ (J (X i j (J (x j)))) (x i) =
      star (inner ℂ (X i j (J (x j))) (J (x i)))
    conv_lhs => rw [← hJ (x i)]
    exact BoundedRecovery.antiunitary_inner J _ _
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (map_nonneg (matrixOperatorHom (n := n) (H := H)) hX)).inner_nonneg_left y
  have hn : 0 ≤ inner ℂ (matrixOperator (antiunitaryMatrix J X) x) x := by
    rw [he]
    exact star_nonneg_iff.mpr hp
  exact ⟨Complex.ext rfl hn.2, hn.1⟩

def antiunitaryCPConjugate (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun T => antiunitaryConjugate J (P (antiunitaryConjugate J T))
      map_add' := by intros; simp only [antiunitaryConjugate_add, map_add]
      map_smul' := by intros; simp only [antiunitaryConjugate_smul, map_smul, star_star,
        RingHom.id_apply] }
    ‖P‖ (fun T => (antiunitaryConjugate_norm_le J _).trans
      ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (antiunitaryConjugate_norm_le J T) (norm_nonneg P))))

lemma antiunitaryCPConjugate_norm_le (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    ‖antiunitaryCPConjugate J P‖ ≤ ‖P‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg P) _

lemma antiunitaryCPConjugate_cp (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hP : CompletelyPositive P) :
    CompletelyPositive (antiunitaryCPConjugate J P) := by
  intro n X hX
  exact antiunitaryMatrix_nonneg J hJ (matrixLinearMap P (antiunitaryMatrix J X))
    (hP n _ (antiunitaryMatrix_nonneg J hJ X hX))

end WeakPureInfiniteness

end

end OAI
