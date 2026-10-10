import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem stdGaussian_orthogonalProjection (E : Submodule ℝ H) :
    (stdGaussian H).map E.orthogonalProjectionOnto = stdGaussian E := by
  apply Measure.ext_of_charFunDual
  ext L
  let x := (InnerProductSpace.toDual ℝ E).symm L
  have hx : L = innerSL ℝ x := by
    ext y
    exact (InnerProductSpace.toDual_symm_apply (x := y) (y := L)).symm
  have hc : L.comp E.orthogonalProjectionOnto = innerSL ℝ (x : H) := by
    ext y
    rw [hx]
    exact E.inner_orthogonalProjectionOnto_eq_of_mem_left x y
  rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian, hc, hx]
  simp only [innerSL_apply_norm, Submodule.norm_coe]

theorem ae_stdGaussian_ne_zero_of_unit {w : H} (hw : ‖w‖ = 1) :
    ∀ᵐ x ∂stdGaussian H, x ≠ 0 := by
  let L : StrongDual ℝ H := innerSL ℝ w
  have hm : (stdGaussian H).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    simp [L, hw]
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have ha : ∀ᵐ y : ℝ ∂(stdGaussian H).map L, y ≠ 0 := by
    rw [hm, ae_iff]
    simp
  have hb : ∀ᵐ x ∂stdGaussian H, L x ≠ 0 :=
    (ae_map_iff L.continuous.measurable.aemeasurable (measurableSet_singleton 0).compl).mp ha
  filter_upwards [hb] with x hx
  intro h
  simp [h] at hx

def normalizedDirection (w x : H) : H := if x = 0 then w else ‖x‖⁻¹ • x

@[fun_prop] theorem measurable_normalizedDirection (w : H) :
    Measurable (normalizedDirection w) := by
  unfold normalizedDirection
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
@[simp] theorem norm_normalizedDirection {w : H} (hw : ‖w‖ = 1) (x : H) :
    ‖normalizedDirection w x‖ = 1 := by
  unfold normalizedDirection
  split_ifs with hx
  · exact hw
  · exact norm_smul_inv_norm hx

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma normalizedDirection_scale {w x : H} (hx : ‖x‖ = 1) {r : ℝ} (hr : 0 < r) :
    normalizedDirection w (r • x) = x := by
  have hxn : x ≠ 0 := by intro h; simp [h] at hx
  rw [normalizedDirection, ite_eq_right (smul_ne_zero hr.ne' hxn), norm_smul, hx,
    Real.norm_eq_abs, abs_of_pos hr, mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
