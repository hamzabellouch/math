import OAI.NumberTheory.Jacobsthal.Probability.SecondLossKernel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem secondKernel_integral {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    (∫ y in Icc (1:ℝ) 3,secondKernel (y,x))=∫ t : ℝ in 1..x,loss2Kernel t x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have h := integrated_force_window x 1 3 x 1 (by norm_num) hx.1 hx.2
    (by linarith [hx.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => secondKernel (y,x))=
      (fun y => (2/x)*((y^2-1)*omissionForce .odd (2*y+2-x) x)) := by
    funext y
    simp only [secondKernel,max_eq_right hx.1]
    ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤3),h,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss2Kernel]
  field_simp
  ring

theorem second_loss_ordered_integral :
    omissionLossTerm 1=∫ x : ℝ in 1..2,∫ t : ℝ in 1..x,loss2Kernel t x := by
  rw [second_loss_bounded]
  simp_rw [second_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤3)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap secondKernel_continuous.measurable 1 3 1 2 16
    (fun _ hy _ hx => secondKernel_bound hy hx)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact secondKernel_integral hx

end ErdosOmissionBindings

end

end Erdos970

end OAI
