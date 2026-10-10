import OAI.NumberTheory.Jacobsthal.Renewal.DickmanMoments

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open NumberTheoryLean.Dickman

theorem lower_deficit_total :
    IntegrableOn lowerDeficit (Ioi 0) ∧ (∫ t in Ioi 0,lowerDeficit t)=sieveA-1 := by
  have h := upper_future_integral (s := 1) le_rfl
  norm_num only [sub_self,one_mul] at h
  refine ⟨h.1,?_⟩
  rw [← h.2]
  simp only [upperDeficit,F_initial sieveA (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤3),div_one]

theorem lower_deficit_shift_tail :
    IntegrableOn (fun y : ℝ => lowerDeficit (y+1)) (Ioi 1) ∧
    (∫ y in Ioi 1,lowerDeficit (y+1))=sieveA-3 := by
  have ht := lower_deficit_total.1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤2))
  have hs := halfline_shift 1 1 lowerDeficit
  norm_num only [one_add_one_eq_two] at hs
  refine ⟨hs.2.mp ht,?_⟩
  rw [← hs.1]
  have hu : (∫ t : ℝ in 0..2,lowerDeficit t)=2 := by
    calc
      _ = ∫ _t : ℝ in 0..2,(1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤2)] at ht
        simp only [lowerDeficit,f_initial sieveA ht.2,sub_zero]
      _ = _ := by norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi lower_deficit_total.1 (by norm_num : (0:ℝ)≤2)
  rw [hu,lower_deficit_total.2] at hsplit
  linarith

theorem shifted_deficit_moments_integrable :
    IntegrableOn (fun y : ℝ => y^2*lowerDeficit (y+1)) (Ioi 0) ∧
    IntegrableOn (fun y : ℝ => y^2*upperDeficit (y+1)) (Ioi 0) := by
  have bound (b : ℝ → ℝ) (hb : ∀ y, 0 < y → 0 ≤ b (y+1) ∧ b (y+1) ≤ sieveA*rho y/(y+1))
      (hc : ContinuousOn (fun y : ℝ => b (y+1)) (Ioi 0)) :
      IntegrableOn (fun y : ℝ => y^2*b (y+1)) (Ioi 0) := by
    apply (rho_quadratic_quotient.1.const_mul sieveA).mono'
      (((continuous_id.pow 2).continuousOn.mul hc).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    change ‖y^2*b (y+1)‖ ≤ sieveA*(y^2*rho y/(y+1))
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg y) (hb y hy0).1)]
    calc
      _ ≤ y^2*(sieveA*rho y/(y+1)) := mul_le_mul_of_nonneg_left (hb y hy0).2 (sq_nonneg y)
      _ = _ := by ring
  have hbound (y : ℝ) (hy : 0 < y) :
      (0 ≤ lowerDeficit (y+1) ∧ lowerDeficit (y+1) ≤ sieveA*rho y/(y+1)) ∧
      (0 ≤ upperDeficit (y+1) ∧ upperDeficit (y+1) ≤ sieveA*rho y/(y+1)) := by
    have hy1 : 1 ≤ y+1 := by linarith
    have hp := deficits_pos hy1
    have he := deficit_sum (y+1)
    rw [gap_eq_rho hy1,add_sub_cancel_right] at he
    exact ⟨⟨hp.1.le,by linarith⟩,⟨hp.2.le,by linarith⟩⟩
  constructor
  · exact bound lowerDeficit (fun y hy => (hbound y hy).1)
      (lowerDeficit_continuous.comp (continuous_id.add continuous_const)).continuousOn
  · apply bound upperDeficit (fun y hy => (hbound y hy).2)
    apply upperDeficit_continuousOn.comp (continuous_id.add continuous_const).continuousOn
    intro y hy
    change 1 ≤ y+1
    change 0 < y at hy
    linarith

theorem shifted_deficit_moment_sum :
    (∫ y in Ioi 0,y^2*lowerDeficit (y+1))+
      (∫ y in Ioi 0,y^2*upperDeficit (y+1))=sieveA := by
  rw [← integral_add shifted_deficit_moments_integrable.1 shifted_deficit_moments_integrable.2]
  have heq : EqOn (fun y : ℝ => y^2*lowerDeficit (y+1)+y^2*upperDeficit (y+1))
      (fun y => sieveA*(y^2*rho y/(y+1))) (Ioi 0) := by
    intro y hy
    dsimp only
    rw [← mul_add,deficit_sum,gap_eq_rho (by change 0 < y at hy; linarith : 1 ≤ y+1),add_sub_cancel_right]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq,integral_const_mul,rho_quadratic_quotient.2,mul_one]

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
