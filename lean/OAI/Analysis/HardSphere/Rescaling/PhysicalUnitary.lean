import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalRescaleLp

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling

lemma pull_complex_smul (N : ℕ) (L J : Length) (z : ℂ) (f : ScalarL2 N J) :
    pull N L J (z • f)=z • pull N L J f := by
  apply Lp.ext
  have hs := (config_preserving N L J).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure (Lp.coeFn_smul z f) (ENNReal.ofReal (jacobian N L J)))
  filter_upwards [pull_ae N L J (z • f),Lp.coeFn_smul z (pull N L J f),
    pull_ae N L J f,hs] with X h₁ h₂ h₃ h₄
  simp only [Function.comp_apply, Pi.smul_apply] at h₂ h₄
  rw [h₁,h₂,h₃,h₄]
  exact smul_comm _ _ _

lemma circle_inverse (L J : Length) (x : AddCircle L.val) :
    circle J L (circle L J x)=x := by
  obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective x
  rw [←ht,circle_project,circle_project]
  congr 1
  field_simp [L.property.ne',J.property.ne']

lemma config_inverse (N : ℕ) (L J : Length) (X : Configuration N L) :
    config N J L (config N L J X)=X := by
  ext i j
  exact circle_inverse L J (X i j)

lemma jacobian_inverse (N : ℕ) (L J : Length) :
    jacobian N L J*jacobian N J L=1 := by
  unfold jacobian
  rw [←mul_pow]
  have h : (L.val^3/J.val^3)*(J.val^3/L.val^3)=(1:ℝ) := by
    field_simp [L.property.ne',J.property.ne']
  rw [h,one_pow]

lemma amplitude_inverse (N : ℕ) (L J : Length) :
    amplitude N L J*amplitude N J L=1 := by
  have h : (amplitude N L J*amplitude N J L)^2=(1:ℝ) := by
    rw [mul_pow,amplitude_sq,amplitude_sq,←mul_inv,jacobian_inverse,inv_one]
  have hp := mul_pos (amplitude_pos N L J) (amplitude_pos N J L)
  nlinarith

lemma pull_inverse (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    pull N J L (pull N L J f)=f := by
  apply Lp.ext
  have hs := (config_preserving N J L).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure (pull_ae N L J f) (ENNReal.ofReal (jacobian N J L)))
  filter_upwards [pull_ae N J L (pull N L J f),hs] with X h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁,h₂,config_inverse,smul_smul,amplitude_inverse,one_smul]

def unitary (N : ℕ) (L J : Length) : ScalarL2 N J ≃ₗᵢ[ℂ] ScalarL2 N L where
  toFun := pull N L J
  invFun := pull N J L
  map_add' := (pull N L J).map_add
  map_smul' := pull_complex_smul N L J
  left_inv := pull_inverse N L J
  right_inv := pull_inverse N J L
  norm_map' := pull_norm N L J

@[simp] lemma unitary_apply (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    unitary N L J f=pull N L J f := rfl

end HardSphere.Rescaling
end
end

end OAI
