import OAI.Analysis.LipschitzHilbert.Fourier.VerticalKernelMoment
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def finiteTimeKernel (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) (t : ℝ) : ℂ :=
  ∑ j : Fin N, scaledTimeKernel k (topLength/(2:ℝ)^j.val) t

theorem schwartz_first_absolute_moment_integrable (k : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => |t| *‖k t‖) := by
  simpa only [pow_one,Real.norm_eq_abs] using k.integrable_pow_mul volume 1

theorem scaledTimeKernel_moment1_pointwise (k : ℝ → ℂ) (l t : ℝ) (hl : 0<l) :
    |t| *‖scaledTimeKernel k l t‖=|t/l| *‖k (t/l)‖ := by
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hl.le,abs_div,abs_of_pos hl]
  ring

theorem scaledTimeKernel_moment1_integrable (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    Integrable (fun t => |t| *‖scaledTimeKernel k l t‖) := by
  have hi := (schwartz_first_absolute_moment_integrable k).comp_mul_right' (inv_ne_zero hl.ne')
  apply hi.congr
  filter_upwards [] with t
  simpa only [div_eq_mul_inv] using (scaledTimeKernel_moment1_pointwise k l t hl).symm

theorem scaledTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    (∫ t, |t| *‖scaledTimeKernel k l t‖)=l*(∫ t, |t| *‖k t‖) := by
  simp_rw [scaledTimeKernel_moment1_pointwise k l _ hl]
  rw [Measure.integral_comp_div (fun t => |t| *‖k t‖) l,abs_of_pos hl,smul_eq_mul]

theorem finiteTimeKernel_measurable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) :
    Measurable (finiteTimeKernel k N topLength) := by
  unfold finiteTimeKernel scaledTimeKernel
  fun_prop

theorem finiteTimeKernel_integrable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) : Integrable (finiteTimeKernel k N topLength) := by
  exact integrable_finsetSum _ (fun j _ => scaledTimeKernel_integrable k k.integrable _
    (ne_of_gt (div_pos htop (pow_pos (by norm_num) j.val))))

theorem finiteTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) :
    Integrable (fun t => |t| *‖finiteTimeKernel k N topLength t‖) ∧
      (∫ t, |t| *‖finiteTimeKernel k N topLength t‖)≤
        2*topLength*(∫ t, |t| *‖k t‖) := by
  have hl (j : Fin N) : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  have hsum : Integrable (fun t => ∑ j : Fin N,
      |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖) :=
    integrable_finsetSum _ (fun j _ => scaledTimeKernel_moment1_integrable k _ (hl j))
  have hp (t : ℝ) : |t| *‖finiteTimeKernel k N topLength t‖≤
      ∑ j : Fin N, |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖ := by
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
  have hi : Integrable (fun t => |t| *‖finiteTimeKernel k N topLength t‖) := by
    apply hsum.mono'
      (((show Continuous (fun t : ℝ => |t|) by fun_prop).measurable.mul
        (finiteTimeKernel_measurable k N topLength).norm).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖|t| *‖finiteTimeKernel k N topLength t‖‖≤_
    simpa only [Real.norm_of_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg _))] using hp t
  have hlength : (∑ j : Fin N, topLength/(2:ℝ)^j.val)≤2*topLength := by
    have heq : (∑ j : Fin N, topLength/(2:ℝ)^j.val)=
        topLength*(∑ j : Fin N, (1/2:ℝ)^j.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv,one_mul,inv_pow]
    rw [heq,Fin.sum_univ_eq_sum_range]
    nlinarith only [mul_le_mul_of_nonneg_left (sum_half_powers_le_two N) htop.le]
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ∑ j : Fin N, |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖ :=
      integral_mono hi hsum hp
    _ = (∑ j : Fin N, topLength/(2:ℝ)^j.val)*(∫ t, |t| *‖k t‖) := by
      rw [integral_finsetSum _ (fun j _ => scaledTimeKernel_moment1_integrable k _ (hl j))]
      simp_rw [scaledTimeKernel_moment1 k _ (hl _)]
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hlength
      (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
