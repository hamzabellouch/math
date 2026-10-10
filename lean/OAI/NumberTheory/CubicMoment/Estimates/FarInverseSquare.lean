import OAI.NumberTheory.CubicMoment.Estimates.InverseSquareTail
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! A fixed smooth inverse-square extension, with all Fourier hypotheses proved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff FourierTransform Topology
namespace CubicFirstMoment

def farInverseSquareReal (x : ℝ) : ℝ := (1-frequencyBump x)*x^(-2:ℤ)

def farInverseSquare (x : ℝ) : ℂ := (farInverseSquareReal x : ℂ)

lemma farInverseSquareReal_eq {x : ℝ} (hx : 1 ≤ |x|) :
    farInverseSquareReal x = x^(-2:ℤ) := by
  have hz : frequencyBump x = 0 := frequencyBump.zero_of_le_dist
    (by simpa only [Real.dist_eq,sub_zero,frequencyBump] using hx)
  simp only [farInverseSquareReal,hz,sub_zero,one_mul]

lemma farInverseSquareReal_smooth : ContDiff ℝ ∞ farInverseSquareReal := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [frequencyBump.eventuallyEq_one] with y hy
    simp only [Pi.one_apply] at hy
    simp only [farInverseSquareReal,hy,sub_self,zero_mul]
  · exact ((contDiff_const.sub frequencyBump.contDiff).contDiffAt).mul
      (by
        simpa only [Pi.inv_apply,id_eq,zpow_neg,zpow_ofNat,inv_pow] using
          ((contDiffAt_id : ContDiffAt ℝ ∞ (fun y : ℝ => y) x).inv hx).pow 2)

lemma farInverseSquare_smooth : ContDiff ℝ ∞ farInverseSquare :=
  Complex.ofRealCLM.contDiff.comp farInverseSquareReal_smooth

lemma farInverseSquareReal_eventually {x : ℝ} (hx : 1 < |x|) :
    farInverseSquareReal =ᶠ[𝓝 x] (fun y : ℝ => y^(-2:ℤ)) := by
  have hn : ∀ᶠ y : ℝ in 𝓝 x, 1 < |y| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds hx
  filter_upwards [hn] with y hy
  exact farInverseSquareReal_eq hy.le

lemma farInverseSquare_deriv_eq : deriv farInverseSquare =
    fun x : ℝ => ((deriv farInverseSquareReal x : ℝ) : ℂ) := by
  funext x
  exact (farInverseSquareReal_smooth.differentiable (by simp) x).hasDerivAt.ofReal_comp.deriv

lemma farInverseSquare_second_deriv_eq : deriv (deriv farInverseSquare) =
    fun x : ℝ => ((deriv (deriv farInverseSquareReal) x : ℝ) : ℂ) := by
  rw [farInverseSquare_deriv_eq]
  funext x
  exact (((contDiff_infty_iff_deriv.mp farInverseSquareReal_smooth).2).differentiable
    (by simp) x).hasDerivAt.ofReal_comp.deriv

lemma farInverseSquareReal_deriv_tail {x : ℝ} (hx : 1 < |x|) :
    deriv farInverseSquareReal x = -2*x^(-3:ℤ) := by
  rw [(farInverseSquareReal_eventually hx).deriv_eq,deriv_zpow]
  norm_num

lemma farInverseSquareReal_second_tail {x : ℝ} (hx : 1 < |x|) :
    deriv (deriv farInverseSquareReal) x = 6*x^(-4:ℤ) := by
  rw [(farInverseSquareReal_eventually hx).deriv.deriv_eq]
  have hd : deriv (fun y : ℝ => y^(-2:ℤ)) = fun y : ℝ => (-2:ℝ)*y^(-3:ℤ) := by
    simpa only [Int.reduceSub,Int.cast_neg,Int.cast_ofNat] using deriv_zpow' (-2:ℤ)
  rw [hd,deriv_const_mul_field']
  change (-2:ℝ)*deriv (fun y : ℝ => y^(-3:ℤ)) x = _
  rw [deriv_zpow]
  norm_num
  ring

lemma farInverseSquare_integrable : Integrable farInverseSquare := by
  apply integrable_of_inverse_square_tail _ farInverseSquare_smooth.continuous
    (C := 1) (by norm_num)
  intro x hx
  rw [farInverseSquare,farInverseSquareReal_eq (by linarith : 1 ≤ |x|),Complex.norm_real]
  simpa only [one_mul] using norm_real_zpow_tail hx (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (-2:ℤ) ≤ -2)

lemma farInverseSquare_deriv_integrable : Integrable (deriv farInverseSquare) := by
  apply integrable_of_inverse_square_tail _ (contDiff_infty_iff_deriv.mp farInverseSquare_smooth).2.continuous
    (C := 2) (by norm_num)
  intro x hx
  simp only [farInverseSquare_deriv_eq]
  rw [farInverseSquareReal_deriv_tail (by linarith : 1 < |x|),Complex.norm_real]
  have hn : ‖(-2:ℝ)*x^(-3:ℤ)‖ = ‖(2:ℝ)*x^(-3:ℤ)‖ := by rw [neg_mul,norm_neg]
  rw [hn]
  exact norm_real_zpow_tail hx (by norm_num) (by norm_num)

lemma farInverseSquare_second_integrable : Integrable (deriv (deriv farInverseSquare)) := by
  apply integrable_of_inverse_square_tail _ (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp farInverseSquare_smooth).2).2.continuous
    (C := 6) (by norm_num)
  intro x hx
  simp only [farInverseSquare_second_deriv_eq]
  rw [farInverseSquareReal_second_tail (by linarith : 1 < |x|),Complex.norm_real]
  exact norm_real_zpow_tail hx (by norm_num) (by norm_num)

lemma farInverseSquare_fourier_integrable : Integrable (𝓕 farInverseSquare) :=
  integrable_fourier_of_two_derivatives _ farInverseSquare_integrable
    (farInverseSquare_smooth.differentiable (by simp)) farInverseSquare_deriv_integrable
    ((contDiff_infty_iff_deriv.mp farInverseSquare_smooth).2.differentiable (by simp)) farInverseSquare_second_integrable

lemma farInverseSquare_fourier_dilation {J : ℝ} (hJ : 0 < J) :
    (∫ t : ℝ, ‖𝓕 (fun x => farInverseSquare (J*x)) t‖) =
      ∫ t : ℝ, ‖𝓕 farInverseSquare t‖ := fourier_dilation_l1 farInverseSquare hJ

end CubicFirstMoment

end

end OAI
