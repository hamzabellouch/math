import Mathlib
import OAI.Geometry.PrescribedPotential.CoordinateBalls
import OAI.Geometry.PrescribedPotential.VolumeNormalization

namespace OAI

/-! Path Coordinate Density. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory Matrix
open scoped ContDiff ComplexOrder
namespace Anticanonical.SourceSmooth
open EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma volumePath_det_upper [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (ht : t ∈ Icc 0 1)
    (hsol : SolvesVolumePath g h t φ b) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    |(g.matrix i z + φ.hessian i z).det.re| ≤
      Real.exp (2*‖(⟨(prescribedForcing g h).value,
        (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖) * g.volumeCoefficient i z := by
  let F : C(X,ℝ) := ⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩
  have hb := volumePath_scalar_bound g h ht hsol
  obtain ⟨hp,he⟩ := hsol
  have hd : 0 < (g.matrix i z + φ.hessian i z).det.re := (Complex.pos_iff.mp (hp i z hz).det_pos).1
  have hg := g.volumeCoefficient_pos i hz
  let x := (A.chart i).symm z
  have hez : Real.log ((g.matrix i z + φ.hessian i z).det.re) - Real.log (g.volumeCoefficient i z) =
      t * F x + b := by
    have hev := he x
    change (g.logRatio (g.deform φ hp)).localExpression i z = _ at hev
    rw [g.logRatio_local _ i hz] at hev
    exact hev
  have hFx : |t * F x| ≤ ‖F‖ := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans
      (by simpa only [Real.norm_eq_abs, one_mul] using F.norm_coe_le_norm x)
  have hbound : t*F x+b ≤ 2*‖F‖ := by
    have h1 := (abs_le.mp hFx).2
    have h2 := (abs_le.mp hb).2
    change b ≤ ‖F‖ at h2
    linarith
  have heq : (g.matrix i z + φ.hessian i z).det.re = Real.exp (t*F x+b)*g.volumeCoefficient i z := by
    calc
      _ = Real.exp (Real.log ((g.matrix i z + φ.hessian i z).det.re)) := (Real.exp_log hd).symm
      _ = Real.exp (t*F x+b+Real.log (g.volumeCoefficient i z)) := by congr 1; linarith
      _ = _ := by rw [Real.exp_add, Real.exp_log hg]
  rw [abs_of_pos hd, heq]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbound) hg.le

namespace CoordinateBall
variable (p : CoordinateBall A)

lemma path_det_bound [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → SolvesVolumePath g h t φ b →
      ∀ z ∈ closedBall p.center (3*p.radius),
        |(g.matrix p.index (coordinateEquiv d z) + φ.hessian p.index (coordinateEquiv d z)).det.re| ≤ K := by
  have hc : ContinuousOn (fun z : EC d => g.volumeCoefficient p.index (coordinateEquiv d z))
      (closedBall p.center (3*p.radius)) := by
    exact ((g.volumeCoefficient_smooth p.index).continuousOn.comp
      (coordinateEquiv d).continuous.continuousOn (fun z hz => by
        have hh := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz)
        simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using hh))
  obtain ⟨B,hB⟩ := (isCompact_closedBall p.center (3*p.radius)).exists_bound_of_continuousOn hc
  let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖
  refine ⟨Real.exp (2*M)*max B 1, mul_pos (Real.exp_pos _) (lt_max_iff.mpr (Or.inr (by norm_num))), ?_⟩
  intro t b φ ht hs z hz
  have hzt : coordinateEquiv d z ∈ (A.chart p.index).target := by
    have hh := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz)
    simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using hh
  apply (volumePath_det_upper g h ht hs p.index hzt).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hbc : |g.volumeCoefficient p.index (coordinateEquiv d z)| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB z hz
  exact (le_abs_self _).trans (hbc.trans (le_max_left _ _))
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
