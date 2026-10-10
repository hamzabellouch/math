import OAI.Geometry.RCD.Heat.HeatWeightedEvaluation
import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction

namespace OAI

/-! # Exponentially weighted L² bounds for canonical heat-kernel rows

Testing the weighted evaluation functional on its own weighted row gives
the dual estimate. The continuous kernel is constructed from the semigroup;
no Gaussian bound is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_weighted_row :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q x : X) (a R r t : ℝ),
      0 ≤ R → 0 < r → -1 ≤ K*r^2 → r^2 < t →
      (∫ y, radialWeight q a R y*(hX.canonicalHeatKernel hn p t x y)^2
        ∂hausdorff n X) ≤
      (C/Real.sqrt ((hausdorff n X).real (ball x r))*
        Real.exp ((a*min (dist q x) R+|a| *r)/2+a^2/4*t))^2 := by
  obtain ⟨C,hC,hbound⟩ := hX.heat_weighted_evaluation hn
  refine ⟨C,hC,?_⟩
  intro q x a R r t hR hr hcurv hrt
  have ht : 0 < t := lt_of_le_of_lt (sq_nonneg r) hrt
  let μ := hausdorff n X
  let k := hX.canonicalHeatKernel hn p
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let F := heatKernelRow μ hX.quadratic hk t x
  have hF : F =ᵐ[μ] k t x := heatKernelRow_coe μ hX.quadratic hk ht x
  have hw := radialWeight_signed_lipschitz q a hR
  let B : ℝ≥0 := ⟨Real.exp (|a| *R), (Real.exp_pos _).le⟩
  have hb (y : X) : |radialWeight q a R y| ≤ B := radialWeight_signed_bound q a hR y
  let V := boundedMultiplier μ (radialWeight q a R) hw.continuous.measurable B hb
  have hV : V =ᵐ[μ] radialWeight q a R := boundedMultiplier_coe μ _ _ _ _
  let f := lpMultiplier μ V F
  have hf : f =ᵐ[μ] fun y => radialWeight q a R y*k t x y := by
    filter_upwards [lpMultiplier_coe μ V F,hV,hF] with y hy hv hr
    simpa only [hv,hr] using hy
  have hfi : Integrable f μ := by
    apply Integrable.congr _ hf.symm
    exact (hk.integrable t ht x).bdd_mul hw.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb y)
  let A := ∫ y, radialWeight q a R y*(k t x y)^2 ∂μ
  have hA : 0 ≤ A := integral_nonneg fun y =>
    mul_nonneg (radialWeight_nonneg q a R y) (sq_nonneg _)
  by_cases hAzero : A = 0
  · change A ≤ _
    rw [hAzero]
    positivity
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  have hsq : (Real.sqrt A)^2 = A := Real.sq_sqrt hA
  have hproduct (y : X) : radialWeight q (-a) R y*radialWeight q a R y = 1 := by
    simp only [radialWeight, ← Real.exp_add]
    rw [show (-a)*min (dist q y) R+a*min (dist q y) R = 0 by ring,Real.exp_zero]
  have hnorm : (∫ y, radialWeight q (-a) R y*(f y)^2 ∂μ) = A := by
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    calc
      _ = (radialWeight q (-a) R y*radialWeight q a R y)*
          radialWeight q a R y*(k t x y)^2 := by ring
      _ = _ := by rw [hproduct y,one_mul]
  have hval : kernelHeat μ hX.quadratic hk t f x = A := by
    rw [kernelHeat_eq_integral μ hX.quadratic hk ht f]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    ring
  have hh := hbound q x (-a) R r t (Real.sqrt A) hR hr hcurv hrt
    (Real.sqrt_pos.mpr hApos) f (kernelHeat μ hX.quadratic hk t f)
    (kernelHeat_continuous μ hX.quadratic hk ht f)
    (kernelHeat_represents μ hX.quadratic hk ht f hfi)
    (by rw [hnorm,hsq])
  rw [hval,abs_of_nonneg hA] at hh
  simp only [neg_neg,abs_neg,neg_sq] at hh
  let D := C/Real.sqrt (μ.real (ball x r))*
    Real.exp ((a*min (dist q x) R+|a| *r)/2+a^2/4*t)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hroot : Real.sqrt A ≤ D := by
    change A ≤ C/Real.sqrt (μ.real (ball x r))*
      (Real.exp ((a*min (dist q x) R+|a| *r)/2+a^2/4*t)*Real.sqrt A) at hh
    have hmul : Real.sqrt A*Real.sqrt A ≤ Real.sqrt A*D := by
      calc
        _ = A := by nlinarith only [hsq]
        _ ≤ _ := by simpa only [D,mul_assoc,mul_comm,mul_left_comm] using hh
    exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hApos)).mp hmul
  change A ≤ D^2
  rw [← hsq]
  exact (sq_le_sq₀ (Real.sqrt_nonneg A) hD).mpr hroot

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
