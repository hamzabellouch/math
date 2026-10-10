import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflection

namespace OAI

/-! Exact interior modulus control for the moving-circle reflection. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma circleReflectionExtension_inside_norm_le {U:Set ℂ} {f:ℂ→ℂ} {c:ℂ} {r:ℝ}
    (hr:0<r) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hf:∀z∈U,1≤‖z‖ → r≤‖f z-c‖) {z:ℂ} (hzU:z∈U) (hzn:‖z‖<1) :
    ‖circleReflectionExtension c r f z-c‖≤r := by
  let g := fun w => (f w-c)/(r:ℂ)
  have hge : 1≤‖g (unitCircleReflection z)‖ := by
    change 1≤‖(f (unitCircleReflection z)-c)/(r:ℂ)‖
    rw [normalized_circle_norm c hr]
    exact (one_le_div hr).mpr
      (hf _ (hs z hzU) (unitCircleReflection_outer (hz z hzU) hzn.le))
  have hsmall : ‖annularCircleReflect g z‖≤1 := by
    rw [annularCircleReflect,ite_eq_right (not_le_of_gt hzn),unitCircleReflection_norm]
    exact (inv_le_one₀ (zero_lt_one.trans_le hge)).mpr hge
  change ‖c+(r:ℂ)*annularCircleReflect g z-c‖≤r
  rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  nlinarith

end CircleDomainRigidity

end

end OAI
