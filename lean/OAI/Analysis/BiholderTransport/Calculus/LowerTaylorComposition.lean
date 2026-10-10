import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LowerTaylor

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasLowerSecondTaylor (fun h => f (a h)) 0 (pullBilinear B A) := by
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  obtain ⟨C,hC,HC⟩ := hO.exists_pos
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  intro ε hε
  have hδ : 0 < ε/(2*C^2) := div_pos hε (by positivity)
  have hB := (bilinear_remainder_of_hasFDerivAt ha ha0 B).def hε
  filter_upwards [ht.eventually (hf _ hδ),HC.bound,hB] with h hh haB hb
  simp only [zero_apply,add_zero] at hh ⊢
  rw [ha0,pullBilinear_apply]
  have hb' : |B (a h) (a h)-B (A h) (A h)| ≤ ε*‖h‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb
  have hsq : ‖a h‖^2 ≤ C^2*‖h‖^2 := by
    nlinarith only [sq_nonneg (C*‖h‖-‖a h‖),haB,norm_nonneg (a h),
      mul_nonneg hC.le (norm_nonneg h)]
  have hsq' := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have he : ε/(2*C^2)*(C^2*‖h‖^2)=(ε/2)*‖h‖^2 := by
    field_simp [hC.ne']
  rw [he] at hsq'
  linarith only [hh,(abs_le.mp hb').1,hsq']

end WeakMTWTransport

end

end OAI
