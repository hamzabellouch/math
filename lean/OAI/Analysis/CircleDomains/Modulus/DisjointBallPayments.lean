import OAI.Analysis.CircleDomains.Selection.ParallelLineIntegration
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! Cauchy--Schwarz for finitely many disjoint payment regions inside
balloons. Only their containing ball areas enter the estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_le_measure_mul_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {m : X → ℝ}
    (hm : MemLp m 2 μ) (hm0 : ∀ x, 0 ≤ m x) :
    (∫ x, m x ∂μ)^2 ≤ μ.real univ*(∫ x, m x^2 ∂μ) := by
  have hb := integral_le_sqrt_measure_mul_L2 hm (Eventually.of_forall hm0)
  have hh := mul_self_le_mul_self (integral_nonneg hm0) hb
  simpa only [← pow_two,mul_pow,Real.sq_sqrt measureReal_nonneg,
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (m x)))] using hh

 theorem sum_disjoint_ball_payments_sq_le {ι : Type*} [DecidableEq ι]
    (F : Finset ι) {E : ι → Set ℂ} {c : ι → ℂ} {d a : ι → ℝ}
    (hd : ∀ j ∈ F, 0 < d j) (hE : ∀ j ∈ F, MeasurableSet (E j))
    (hdisj : Set.Pairwise (↑F) (Disjoint on E))
    (hsub : ∀ j ∈ F, E j ⊆ ball (c j) (d j))
    {m : ℂ → ℝ} (hm : MemLp m 2 volume) (hm0 : ∀ z, 0 ≤ m z) :
    (∑ j ∈ F, a j/d j*(∫ x in E j, m x))^2 ≤
      Real.pi*(∑ j ∈ F, a j^2)*(∫ x, m x^2) := by
  have hpiece (j : ι) (hj : j ∈ F) :
      (a j/d j*(∫ x in E j, m x))^2 ≤ (Real.pi*a j^2)*(∫ x in E j, m x^2) := by
    have hEf : volume (E j) ≠ ∞ := measure_ne_top_of_subset (hsub j hj) measure_ball_lt_top.ne
    let : IsFiniteMeasure (volume.restrict (E j)) := isFiniteMeasure_restrict.mpr hEf
    have hh := integral_sq_le_measure_mul_energy (hm.restrict (E j)) hm0
    rw [Measure.real,Measure.restrict_apply_univ] at hh
    have harea : volume.real (E j) ≤ Real.pi*d j^2 := by
      exact (measureReal_mono (hsub j hj) measure_ball_lt_top.ne).trans_eq (real_volume_ball _ (hd j hj).le)
    have hh' : (∫ x in E j, m x)^2 ≤ Real.pi*d j^2*(∫ x in E j, m x^2) :=
      hh.trans (mul_le_mul_of_nonneg_right harea (integral_nonneg (fun _ => sq_nonneg _)))
    calc
      _ = (a j)^2/(d j)^2*(∫ x in E j, m x)^2 := by ring
      _ ≤ (a j)^2/(d j)^2*(Real.pi*d j^2*(∫ x in E j, m x^2)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = _ := by field_simp [ne_of_gt (hd j hj)]
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
    (fun j _ => mul_nonneg Real.pi_pos.le (sq_nonneg (a j)))
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) hpiece
  have hunion : (∑ j ∈ F, ∫ x in E j, m x^2) ≤ ∫ x, m x^2 := by
    rw [← integral_biUnion_finset F hE hdisj (fun _ _ => hm.integrable_sq.restrict)]
    exact setIntegral_le_integral hm.integrable_sq (Eventually.of_forall (fun x => sq_nonneg (m x)))
  have hsum : (∑ j ∈ F, Real.pi*a j^2) = Real.pi*(∑ j ∈ F, a j^2) :=
    (Finset.mul_sum F (fun j => a j^2) Real.pi).symm
  rw [hsum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hunion (mul_nonneg Real.pi_pos.le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

end CircleDomainRigidity

end

end OAI
