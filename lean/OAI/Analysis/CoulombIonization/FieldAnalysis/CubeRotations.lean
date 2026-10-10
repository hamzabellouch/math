import Mathlib

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeRotations_scope

open MeasureTheory Set
open scoped BigOperators

abbrev CubeSpace := EuclideanSpace ℝ (Fin 3)

abbrev CubeRotation := unitary (CubeSpace →L[ℝ] CubeSpace)

instance cubeSpace_continuousStar : ContinuousStar (CubeSpace →L[ℝ] CubeSpace) :=
  ⟨(ContinuousLinearMap.adjoint : (CubeSpace →L[ℝ] CubeSpace) ≃ₗᵢ⋆[ℝ] _).continuous⟩

instance cubeRotation_compact : CompactSpace CubeRotation := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : CubeSpace →L[ℝ] CubeSpace) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (CStarRing.norm_coe_unitary (⟨u,hu⟩ : CubeRotation)).le

def cubeRotationMeasure : Measure CubeRotation :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts CubeRotation)

instance cubeRotation_probability : IsProbabilityMeasure cubeRotationMeasure :=
  ⟨by exact Measure.haarMeasure_self⟩

instance cubeRotation_leftInvariant : cubeRotationMeasure.IsMulLeftInvariant := by
  unfold cubeRotationMeasure
  infer_instance

def rotationIsometry (R : CubeRotation) : CubeSpace ≃ₗᵢ[ℝ] CubeSpace :=
  Unitary.linearIsometryEquiv R

@[simp] lemma rotationIsometry_apply (R : CubeRotation) (x : CubeSpace) :
    rotationIsometry R x = (R : CubeSpace →L[ℝ] CubeSpace) x := rfl

lemma rotationIsometry_continuous : Continuous (fun p : CubeRotation × CubeSpace => rotationIsometry p.1 p.2) :=
  Continuous.clm_apply (continuous_subtype_val.comp continuous_fst) continuous_snd

lemma rotationIsometry_inv_mul (R S : CubeRotation) (x : CubeSpace) :
    rotationIsometry (S*R)⁻¹ (rotationIsometry S x) = rotationIsometry R⁻¹ x := by
  have he : (S*R)⁻¹*S = R⁻¹ := by simp
  have hh := congrArg (fun U : CubeRotation => rotationIsometry U x) he
  exact hh

end Work_CubeRotations_scope

open MeasureTheory Set Filter
open scoped BigOperators

def radialAverage (k : CubeSpace → ℝ) (x : CubeSpace) : ℝ :=
  ∫ R : CubeRotation, k (rotationIsometry R⁻¹ x) ∂cubeRotationMeasure

lemma radialAverage_joint_measurable {k : CubeSpace → ℝ} (hk : Measurable k) :
    Measurable (fun p : CubeRotation × CubeSpace => k (rotationIsometry p.1⁻¹ p.2)) :=
  hk.comp (rotationIsometry_continuous.comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd)).measurable

lemma radialAverage_measurable {k : CubeSpace → ℝ} (hk : Measurable k) :
    Measurable (radialAverage k) :=
  (radialAverage_joint_measurable hk).stronglyMeasurable.integral_prod_left'.measurable

lemma radialAverage_section_integrable {k : CubeSpace → ℝ} (hk : Measurable k)
    {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) (x : CubeSpace) :
    Integrable (fun R : CubeRotation => k (rotationIsometry R⁻¹ x)) cubeRotationMeasure := by
  apply (integrable_const B).mono'
    ((radialAverage_joint_measurable hk).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun R => hB _)

lemma radialAverage_nonneg {k : CubeSpace → ℝ} (hk : ∀ x, 0 ≤ k x) (x : CubeSpace) :
    0 ≤ radialAverage k x := integral_nonneg (fun _ => hk _)

lemma radialAverage_le {k : CubeSpace → ℝ} (hm : Measurable k) (hn : ∀ x, 0 ≤ k x)
    {B : ℝ} (hB : ∀ x, k x ≤ B) (x : CubeSpace) : radialAverage k x ≤ B := by
  have hi := radialAverage_section_integrable hm (fun x => by rw [Real.norm_of_nonneg (hn x)]; exact hB x) x
  calc
    _ ≤ ∫ _R : CubeRotation, B ∂cubeRotationMeasure :=
      integral_mono hi (integrable_const _) (fun _ => hB _)
    _ = B := by simp

lemma radialAverage_rotation (k : CubeSpace → ℝ) (S : CubeRotation) (x : CubeSpace) :
    radialAverage k (rotationIsometry S x) = radialAverage k x := by
  unfold radialAverage
  rw [←integral_mul_left_eq_self (fun R : CubeRotation => k (rotationIsometry R⁻¹ (rotationIsometry S x))) S]
  simp only [rotationIsometry_inv_mul]

lemma radialAverage_radial (k : CubeSpace → ℝ) {x y : CubeSpace} (h : ‖x‖ = ‖y‖) :
    radialAverage k x = radialAverage k y := by
  let S : CubeRotation := Unitary.linearIsometryEquiv.symm ((ℝ ∙ (x-y))ᗮ.reflection)
  have he : rotationIsometry S x = y := by
    change (Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm _)) x = y
    rw [MulEquiv.apply_symm_apply]
    exact Submodule.reflection_sub h
  rw [←he,radialAverage_rotation]

lemma radialAverage_support {k : CubeSpace → ℝ} {r : ℝ}
    (hs : ∀ x, r ≤ ‖x‖ → k x = 0) (x : CubeSpace) (hx : r ≤ ‖x‖) :
    radialAverage k x = 0 := by
  unfold radialAverage
  have he (R : CubeRotation) : k (rotationIsometry R⁻¹ x) = 0 :=
    hs _ (by simpa only [LinearIsometryEquiv.norm_map] using hx)
  simp only [he,integral_zero]

lemma radialAverage_joint_integrable {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    Integrable (fun p : CubeRotation × CubeSpace => k (rotationIsometry p.1⁻¹ p.2))
      (cubeRotationMeasure.prod volume) := by
  apply (integrable_prod_iff (radialAverage_joint_measurable hm).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun R => ((rotationIsometry R⁻¹).measurePreserving.integrable_comp hk.aestronglyMeasurable).2 hk)
  · have he (R : CubeRotation) : (∫ x, ‖k (rotationIsometry R⁻¹ x)‖) = ∫ x, ‖k x‖ :=
      (rotationIsometry R⁻¹).measurePreserving.integral_comp
        (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding (fun x => ‖k x‖)
    simp only [he]
    exact integrable_const _

lemma radialAverage_integrable {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    Integrable (radialAverage k) := (radialAverage_joint_integrable hm hk).integral_prod_right

lemma integral_radialAverage {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    (∫ x, radialAverage k x) = ∫ x, k x := by
  unfold radialAverage
  rw [←integral_integral_swap (radialAverage_joint_integrable hm hk)]
  have he (R : CubeRotation) : (∫ x, k (rotationIsometry R⁻¹ x)) = ∫ x, k x :=
    (rotationIsometry R⁻¹).measurePreserving.integral_comp
      (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding k
  simp only [he]
  simp

end CoulombNeumann

end

end OAI
