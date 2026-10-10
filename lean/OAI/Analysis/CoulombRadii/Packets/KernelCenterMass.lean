import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonSubmean
import OAI.Analysis.CoulombRadii.Packets.KernelScale

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace NeutralAtom

lemma continuous_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z) (y : Coulomb.Space) :
    Continuous (fun z => scaledCenterKernel φ t z y) := by
  unfold scaledCenterKernel
  exact ((htc.pow 3).inv₀ (fun z => pow_ne_zero _ (ht z).ne')).mul
    (hφ.comp ((htc.inv₀ (fun z => (ht z).ne')).smul (continuous_const.sub continuous_id)))

lemma integrable_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0)
    (hLip : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4) (y : Coulomb.Space) :
    Integrable (fun z => scaledCenterKernel φ t z y) := by
  apply (continuous_scaledCenterKernel hφ htc ht y).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Metric.closedBall y (2*t y)) (isCompact_closedBall _ _)
  intro z hz
  by_contra hK
  have hh := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).2
  apply hz
  rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
  linarith [ht y]

lemma integral_constant_scaledCenterKernel (φ : Coulomb.Space → ℝ)
    {T : ℝ} (hT : 0 < T) (y : Coulomb.Space) :
    (∫ z, scaledCenterKernel φ (fun _ => T) z y) = ∫ z, φ z := by
  unfold scaledCenterKernel
  rw [integral_const_mul, integral_sub_left_eq_self
    (fun z : Coulomb.Space => φ (T⁻¹ • z)),
    Measure.integral_comp_inv_smul_of_nonneg volume φ hT.le]
  simp only [Coulomb.Space,finrank_euclideanSpace_fin,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hT.ne'),one_mul]

theorem center_kernel_mass_defect {φ t : Coulomb.Space → ℝ} {B L q : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hq : 0 ≤ q) (hqs : q ≤ 1/4)
    (hφc : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (hLip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖)
    (y : Coulomb.Space) :
    |(∫ z, scaledCenterKernel φ t z y)-(∫ z, φ z)| ≤
      (64*Real.pi/3)*(48*B+64*L)*q := by
  have hT := ht y
  have hLip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hLip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hqs (norm_nonneg _)
      _ = _ := by ring
  let F : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ t z y
  let G : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ (fun _ => t y) z y
  have hFi : Integrable F := integrable_scaledCenterKernel hφc htc ht hs hLip' y
  have hGi : Integrable G := integrable_scaledCenterKernel hφc continuous_const (fun _ => hT) hs
    (by intro z z'; simp only [sub_self,abs_zero]; positivity) y
  have hpt (z : Coulomb.Space) (hz : z∈Metric.closedBall y (2*t y)) :
      |F z-G z| ≤ 2*(48*B+64*L)*q/(t y)^3 := by
    have hz' : ‖y-z‖ ≤ 2*t y := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    have hwd : |t z-t y| ≤ 2*q*t y := by
      calc
        _ ≤ q*‖z-y‖ := hLip z y
        _ ≤ q*(2*t y) := mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hz') hq
        _ = _ := by ring
    have ha : t y/2 ≤ t z := by
      have hab := abs_le.mp hwd
      have hqt := mul_le_mul_of_nonneg_right hqs hT.le
      nlinarith
    have hh := scaled_kernel_local_bound hT ha (show t y/2 ≤ t y by linarith) hB hL φ hφ hφL
      (y-z) (y-z) hz'
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    calc
      _ ≤ ((48*B+64*L)/(t y)^4)*|t z-t y| := hh
      _ ≤ ((48*B+64*L)/(t y)^4)*(2*q*t y) := mul_le_mul_of_nonneg_left hwd (by positivity)
      _ = _ := by field_simp
  have hout (z : Coulomb.Space) (hz : z∉Metric.closedBall y (2*t y)) : F z-G z=0 := by
    have hz' : 2*t y < ‖y-z‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev,not_le] using hz
    have hF : F z=0 := by
      by_contra hh
      have hh' := (scaledCenterKernel_support_width φ t hs ht hLip' z y hh).2
      linarith
    have hG : G z=0 := by
      by_contra hh
      have hh' := scaledCenterKernel_support φ (fun _ => t y) hs (fun _ => hT) z y hh
      linarith
    rw [hF,hG,sub_self]
  rw [←integral_constant_scaledCenterKernel φ hT y,←integral_sub hFi hGi]
  change |∫ z, F z-G z| ≤ _
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (isCompact_closedBall y (2*t y)).measure_lt_top
    (fun z hz => (show ‖F z-G z‖ ≤ 2*(48*B+64*L)*q/(t y)^3 by simpa only [Real.norm_eq_abs] using hpt z hz))
  rw [Real.norm_eq_abs,Coulomb.volume_closedBall_three y (by positivity : 0 ≤ 2*t y)] at hh
  apply hh.trans_eq
  field_simp
  ring

end NeutralAtom
end

end
end

end OAI
