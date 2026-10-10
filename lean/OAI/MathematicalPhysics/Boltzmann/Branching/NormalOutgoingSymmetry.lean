import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereAntipodal

namespace OAI

section

/-! # The actual normal-angle law is half the uniform sphere area measure -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem normalReflection_neg (e n : Sphere) : normalReflection e (-n) = normalReflection e n := by
  apply Subtype.ext
  exact normalReflection_neg_normal e n

theorem normalReflection_split (e n : Sphere) (f : Sphere → ℝ≥0∞) :
    ENNReal.ofReal |inner ℝ e.1 n.1| * f (normalReflection e n) =
      positiveReflectionTest e f n+positiveReflectionTest e f (-n) := by
  simp only [positiveReflectionTest,show (-n).1 = -n.1 from rfl,inner_neg_right,normalReflection_neg]
  by_cases h : 0 < inner ℝ e.1 n.1
  · simp [h,not_lt.mpr (neg_nonpos.mpr h.le),abs_of_pos h]
  · have hh : inner ℝ e.1 n.1 ≤ 0 := le_of_not_gt h
    by_cases hn : inner ℝ e.1 n.1 < 0
    · simp [h,neg_pos.mpr hn,abs_of_neg hn]
    · have hz : inner ℝ e.1 n.1 = 0 := le_antisymm hh (le_of_not_gt hn)
      simp [hz]

theorem normalReflectionLaw_north : normalReflectionLaw northSphere = (2:ℝ≥0∞)⁻¹ • sphereArea := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalReflectionLaw_lintegral _ hf,lintegral_smul_measure]
  simp_rw [normalReflection_split]
  rw [lintegral_add_left (positiveReflectionTest_measurable northSphere hf)]
  have hn : (∫⁻ n, positiveReflectionTest northSphere f (-n) ∂sphereArea) =
      ∫⁻ n, positiveReflectionTest northSphere f n ∂sphereArea := by
    have hm := positiveReflectionTest_measurable northSphere hf
    rw [← lintegral_map hm measurable_neg,sphereArea_antipodal.map_eq]
  rw [hn]
  have h := positive_hemisphere_reflection f hf
  rw [h]
  rw [← two_mul,smul_eq_mul,← mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem normalReflectionLaw_uniform (e : Sphere) :
    normalReflectionLaw e = (2:ℝ≥0∞)⁻¹ • sphereArea := by
  let R : Velocity ≃ₗᵢ[ℝ] Velocity := (ℝ ∙ (northSphere.1-e.1))ᗮ.reflection
  have he : R northSphere.1 = e.1 := by
    apply Submodule.reflection_sub
    rw [mem_sphere_zero_iff_norm.mp northSphere.property,mem_sphere_zero_iff_norm.mp e.property]
  have he' : sphereIsometry R northSphere = e := Subtype.ext he
  rw [← he',← normalReflectionLaw_isometry,normalReflectionLaw_north,Measure.map_smul,
    (sphereIsometry_measurePreserving R).map_eq]
  exact (sphereIsometry R).measurable.aemeasurable

end BoltzmannNonuniqueness

end

end

section

/-! # Exact normal-angle and outgoing-sphere integrals for a fixed collision pair -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness

theorem normal_left_integral_of_direction (e : Sphere) {r : ℝ} (hr : 0 ≤ r)
    (v w : Velocity) (hg : v-w = r • e.1) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = (ENNReal.ofReal r*(2:ℝ≥0∞)⁻¹)*
        ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  have hc : Measurable (fun n : Sphere => f (child v w n.1)) := by
    apply hf.comp
    unfold child
    fun_prop
  have h := congrArg (fun μ : Measure Sphere => ∫⁻ n, f (child v w n.1) ∂μ)
    (normalReflectionLaw_uniform e)
  rw [normalReflectionLaw_lintegral e hc,lintegral_smul_measure] at h
  simp_rw [normalReflection_child e r hr v w hg] at h
  rw [smul_eq_mul] at h
  have hsc : Measurable (fun n : Sphere => scatterLeft v w n.1) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hm : Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1| * f (scatterLeft v w n.1)) :=
    (show Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1|) by fun_prop).mul
      (hf.comp hsc)
  calc
    _ = ∫⁻ n : Sphere, ENNReal.ofReal r*
        (ENNReal.ofReal |inner ℝ e.1 n.1| * f (scatterLeft v w n)) ∂sphereArea := by
      apply lintegral_congr
      intro n
      unfold collisionKernel normalComponent
      rw [hg,real_inner_smul_left,abs_mul,abs_of_nonneg hr,ENNReal.ofReal_mul hr]
      exact mul_assoc _ _ _
    _ = _ := by
      rw [lintegral_const_mul _ hm,h,mul_assoc]

theorem normal_left_integral (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = (ENNReal.ofReal ‖v-w‖*(2:ℝ≥0∞)⁻¹)*
        ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  by_cases h : v-w = 0
  · simp [collisionKernel,normalComponent,h]
  · let e := sphereDirection northSphere (v-w)
    apply normal_left_integral_of_direction e (norm_nonneg _) v w _ hf
    change v-w = ‖v-w‖ • (sphereDirection northSphere (v-w)).1
    rw [sphereDirection,dite_eq_right h,NormedSpace.norm_smul_normalize]

theorem outgoing_lintegral (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f u ∂outgoing (v,w)) = (ENNReal.ofReal (4*Real.pi))⁻¹*
      ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  rw [outgoing_apply,lintegral_map hf (by unfold child; fun_prop),sphereProbability,
    lintegral_smul_measure,smul_eq_mul]

theorem normal_left_integral_outgoing (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = ENNReal.ofReal (2*Real.pi*‖v-w‖)*∫⁻ u, f u ∂outgoing (v,w) := by
  rw [normal_left_integral v w hf,outgoing_lintegral v w hf,← mul_assoc]
  congr 1
  have hp : 0 < 4*Real.pi := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp,← ENNReal.ofReal_mul (by positivity)]
  have hreal : 2*Real.pi*‖v-w‖*(4*Real.pi)⁻¹ = ‖v-w‖/2 := by field_simp; ring
  rw [hreal,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
  norm_num [div_eq_mul_inv]

end BoltzmannNonuniqueness

end

end

section

/-! # Both normal-angle collision children have the same outgoing law -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness

theorem scatterRight_eq_left_swap (v w n : Velocity) :
    scatterRight v w n = scatterLeft w v n := by
  unfold scatterRight scatterLeft normalComponent
  rw [show w-v = -(v-w) by abel,inner_neg_left]
  module

theorem collisionKernel_swap (v w : Velocity) (n : Sphere) :
    collisionKernel v w n = collisionKernel w v n := by
  unfold collisionKernel normalComponent
  rw [show w-v = -(v-w) by abel,inner_neg_left,abs_neg]

theorem child_swap (v w n : Velocity) : child v w n = child w v n := by
  unfold child
  rw [norm_sub_rev w v,add_comm w v]

theorem outgoing_swap (v w : Velocity) : outgoing (v,w) = outgoing (w,v) := by
  rw [outgoing_apply,outgoing_apply]
  congr 1
  funext n
  exact child_swap v w n.1

theorem normal_right_integral_outgoing (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterRight v w n)
      ∂sphereArea) = ENNReal.ofReal (2*Real.pi*‖v-w‖)*∫⁻ u, f u ∂outgoing (v,w) := by
  simp_rw [scatterRight_eq_left_swap,collisionKernel_swap v w]
  rw [normal_left_integral_outgoing w v hf,norm_sub_rev,outgoing_swap w v]

end BoltzmannNonuniqueness

end

end

end OAI
