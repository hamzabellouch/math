import OAI.Analysis.OperatorAlgebra.ComplexSymmetricMean
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Averaging a strongly continuous unitary orbit using the concrete
symmetric-interval mean. The operator is reconstructed from its bounded
matrix coefficients; no normality of the averaging map is asserted. -/

noncomputable section
open Filter
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def unitaryOrbitCoefficient (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => inner ℂ (T (U t x)) (U t y))
    ((T.continuous.comp (hU x)).inner (hU y)) (‖T‖ * ‖x‖ * ‖y‖) (by
      intro t
      calc
        ‖inner ℂ (T (U t x)) (U t y)‖ ≤ ‖T (U t x)‖ * ‖U t y‖ := norm_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖U t x‖) * ‖U t y‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [(U t).norm_map, (U t).norm_map])

@[simp] lemma unitaryOrbitCoefficient_apply (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) (t : ℝ) :
    unitaryOrbitCoefficient U hU T x y t = inner ℂ (T (U t x)) (U t y) := rfl

lemma unitaryOrbitCoefficient_norm_le (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) :
    ‖unitaryOrbitCoefficient U hU T x y‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [LinearIsometryEquiv.norm_map] using
      mul_le_mul_of_nonneg_right (T.le_opNorm (U t x)) (norm_nonneg (U t y)))

private def unitaryMeanForm (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) : ℂ :=
  complexSymmetricMean ω (unitaryOrbitCoefficient U hU T x y)

private lemma unitaryMeanForm_add_right (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y z : H) :
    unitaryMeanForm ω U hU T x (y + z) =
      unitaryMeanForm ω U hU T x y + unitaryMeanForm ω U hU T x z := by
  have h : unitaryOrbitCoefficient U hU T x (y + z) =
      unitaryOrbitCoefficient U hU T x y + unitaryOrbitCoefficient U hU T x z := by
    ext t
    simp only [unitaryOrbitCoefficient_apply, map_add, inner_add_right,
      BoundedContinuousFunction.add_apply]
  exact (congrArg (complexSymmetricMean ω) h).trans (complexSymmetricMean_add ω _ _)

private lemma unitaryMeanForm_smul_right (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) (c : ℂ) :
    unitaryMeanForm ω U hU T x (c • y) = c * unitaryMeanForm ω U hU T x y := by
  have h : unitaryOrbitCoefficient U hU T x (c • y) =
      c • unitaryOrbitCoefficient U hU T x y := by
    ext t
    simp only [unitaryOrbitCoefficient_apply, map_smul, inner_smul_right,
      BoundedContinuousFunction.smul_apply, smul_eq_mul]
  exact (congrArg (complexSymmetricMean ω) h).trans (complexSymmetricMean_smul ω _ _)

private lemma unitaryMeanForm_bound (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) :
    ‖unitaryMeanForm ω U hU T x y‖ ≤ (2 * ‖T‖ * ‖x‖) * ‖y‖ := by
  exact (complexSymmetricMean_norm_le ω _).trans
    ((mul_le_mul_of_nonneg_left (unitaryOrbitCoefficient_norm_le U hU T x y)
      (by norm_num)).trans_eq (by ring))

private def unitaryMeanFunctional (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x : H) : H →L[ℂ] ℂ :=
  ({ toFun := unitaryMeanForm ω U hU T x
     map_add' := unitaryMeanForm_add_right ω U hU T x
     map_smul' := fun c y => unitaryMeanForm_smul_right ω U hU T x y c } : H →ₗ[ℂ] ℂ).mkContinuous
    (2 * ‖T‖ * ‖x‖) (unitaryMeanForm_bound ω U hU T x)

variable [CompleteSpace H]

private def unitaryMeanLinear (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) : H →ₗ[ℂ] H where
  toFun x := (InnerProductSpace.toDual ℂ H).symm (unitaryMeanFunctional ω U hU T x)
  map_add' x z := by
    apply ext_inner_right ℂ
    intro y
    simp only [InnerProductSpace.toDual_symm_apply, inner_add_left]
    have h : unitaryOrbitCoefficient U hU T (x + z) y =
        unitaryOrbitCoefficient U hU T x y + unitaryOrbitCoefficient U hU T z y := by
      ext t
      simp only [unitaryOrbitCoefficient_apply, map_add, inner_add_left,
        BoundedContinuousFunction.add_apply]
    exact (congrArg (complexSymmetricMean ω) h).trans (complexSymmetricMean_add ω _ _)
  map_smul' c x := by
    apply ext_inner_right ℂ
    intro y
    simp only [InnerProductSpace.toDual_symm_apply, inner_smul_left, RingHom.id_apply]
    have h : unitaryOrbitCoefficient U hU T (c • x) y =
        star c • unitaryOrbitCoefficient U hU T x y := by
      ext t
      simp only [unitaryOrbitCoefficient_apply, map_smul, inner_smul_left,
        BoundedContinuousFunction.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact (congrArg (complexSymmetricMean ω) h).trans (complexSymmetricMean_smul ω _ _)

def unitaryOrbitMean (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (unitaryMeanLinear ω U hU T).mkContinuous (2 * ‖T‖) (fun x => by
    change ‖(InnerProductSpace.toDual ℂ H).symm (unitaryMeanFunctional ω U hU T x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _)

lemma unitaryOrbitMean_inner (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) (x y : H) :
    inner ℂ (unitaryOrbitMean ω U hU T x) y =
      complexSymmetricMean ω (unitaryOrbitCoefficient U hU T x y) :=
  InnerProductSpace.toDual_symm_apply

lemma unitaryOrbitMean_norm_le (ω : Ultrafilter ℕ) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, Continuous (fun t => U t x)) (T : H →L[ℂ] H) :
    ‖unitaryOrbitMean ω U hU T‖ ≤ 2 * ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end WeakPureInfiniteness

end

end OAI
