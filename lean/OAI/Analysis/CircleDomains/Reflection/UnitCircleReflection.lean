import OAI.Analysis.CircleDomains.Reflection.HolomorphicCircleGluing
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! The explicit reflection in the unit circle, with the exact side and
continuity facts used in annular Schwarz reflection. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

def unitCircleReflection (z:ℂ) : ℂ := (conj z)⁻¹

lemma unitCircleReflection_norm (z:ℂ) : ‖unitCircleReflection z‖=‖z‖⁻¹ := by
  simp only [unitCircleReflection,norm_inv,norm_conj]

lemma unitCircleReflection_involutive : Involutive unitCircleReflection := by
  intro z
  simp [unitCircleReflection]

lemma unitCircleReflection_ne_zero {z:ℂ} (hz:z≠0) : unitCircleReflection z≠0 := by
  simpa only [unitCircleReflection,ne_eq,inv_eq_zero,map_eq_zero] using hz

lemma unitCircleReflection_fixed {z:ℂ} (hz:‖z‖=1) : unitCircleReflection z=z := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_comm,Complex.mul_conj',hz]
  norm_num

lemma continuousOn_unitCircleReflection {U:Set ℂ} (hz:∀z∈U,z≠0) :
    ContinuousOn unitCircleReflection U :=
  continuous_conj.continuousOn.inv₀ (fun z h => by simpa using hz z h)

lemma unitCircleReflection_outer {z:ℂ} (hz:z≠0) (hn:‖z‖≤1) :
    1≤‖unitCircleReflection z‖ := by
  rw [unitCircleReflection_norm]
  exact (one_le_inv₀ (norm_pos_iff.mpr hz)).mpr hn

lemma unitCircleReflection_strict_outer {z:ℂ} (hz:z≠0) (hn:‖z‖<1) :
    1<‖unitCircleReflection z‖ := by
  rw [unitCircleReflection_norm]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz)).mpr hn

end CircleDomainRigidity

end

end OAI
