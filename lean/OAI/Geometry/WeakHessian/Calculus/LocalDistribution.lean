import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.LocalMidpoint
import OAI.Geometry.WeakHessian.Calculus.ScalarLocalBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma local_midpoint_implies_curve_bound {F G : X → ℝ} (hFc : Continuous F) (hGc : Continuous G)
    (hmid : ∀ γ : Curve X,IsGeodesic γ → ∀ R c : ℝ,0 < R →
      dist (γ timeZero) (γ timeOne) < R →
      (∀ z,dist z (γ timeHalf) < R → G z ≤ c) →
      (F (γ timeZero)+F (γ timeOne))/2-c/8*dist (γ timeZero) (γ timeOne)^2 ≤ F (γ timeHalf))
    (σ : Curve X) (hσ : IsGeodesic σ) : CurveSecondDerivativeBound F G σ := by
  let D := dist (σ timeZero) (σ timeOne)
  have hD : 0 ≤ D := dist_nonneg
  have hσr : Continuous (evalReal σ) :=
    continuous_evalReal.comp (continuous_const.prodMk continuous_id)
  have hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 →
        secondDifference (F ∘ evalReal σ) h x ≤ D^2*G (evalReal σ x)+ε := by
    intro ε hε
    let e := ε/(D^2+1)
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨η,hη,hηs⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall (σ timeZero) (D+1)).uniformContinuousOn_of_continuous hGc.continuousOn) e he
    let R := min η 1
    have hR : 0 < R := lt_min hη zero_lt_one
    refine ⟨R/(2*(D+1)),by positivity,?_⟩
    intro h hh hhR x hm hp
    have hx : x ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hm.1,hp.2]
    let u : Time := ⟨x-h,hm.1.le,hm.2.le⟩
    let v : Time := ⟨x+h,hp.1.le,hp.2.le⟩
    let γ := restrictCurve u v σ
    have hγ : IsGeodesic γ := hσ.restrictCurve u v
    have hg0 : γ timeZero = evalReal σ (x-h) := by
      rw [restrictCurve_zero]
      congr 1
      apply Subtype.ext
      exact (clampTime_of_mem ⟨hm.1.le,hm.2.le⟩).symm
    have hg1 : γ timeOne = evalReal σ (x+h) := by
      rw [restrictCurve_one]
      congr 1
      apply Subtype.ext
      exact (clampTime_of_mem ⟨hp.1.le,hp.2.le⟩).symm
    have hgm : γ timeHalf = evalReal σ x := by
      change σ (affineTime u v timeHalf) = σ (clampTime x)
      congr 1
      apply Subtype.ext
      rw [clampTime_of_mem hx]
      dsimp [affineTime,u,v,timeHalf]
      ring
    have hlen : dist (γ timeZero) (γ timeOne) = 2*h*D := by
      rw [restrictCurve_zero,restrictCurve_one,hσ u v]
      change |(x-h)-(x+h)| *D = 2*h*D
      rw [abs_of_nonpos (by linarith)]
      ring
    have hshort : dist (γ timeZero) (γ timeOne) < R := by
      rw [hlen]
      have H := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*(D+1))).mp hhR
      nlinarith
    have hnear : ∀ z,dist z (γ timeHalf) < R → G z ≤ G (evalReal σ x)+e := by
      intro z hz
      rw [hgm] at hz
      have hcenter : dist (evalReal σ x) (σ timeZero) ≤ D :=
        geodesic_dist_initial_le hσ (clampTime x)
      have hzB : z ∈ Metric.closedBall (σ timeZero) (D+1) := by
        apply Metric.mem_closedBall.mpr
        have HR : R ≤ 1 := min_le_right η 1
        have H := dist_triangle z (evalReal σ x) (σ timeZero)
        linarith
      have hxB : evalReal σ x ∈ Metric.closedBall (σ timeZero) (D+1) := by
        apply Metric.mem_closedBall.mpr
        linarith
      have H := hηs z hzB (evalReal σ x) hxB (hz.trans_le (min_le_left η 1))
      rw [Real.dist_eq] at H
      linarith [(abs_lt.mp H).2]
    have H := hmid γ hγ R (G (evalReal σ x)+e) hR hshort hnear
    rw [hlen,hg0,hg1,hgm] at H
    have H' : secondDifference (F ∘ evalReal σ) h x ≤ D^2*(G (evalReal σ x)+e) := by
      apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
      change F (evalReal σ (x+h))+F (evalReal σ (x-h))-2*F (evalReal σ x) ≤ _
      nlinarith only [H]
    apply H'.trans
    have hE : D^2*e ≤ ε := by
      dsimp [e]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ) < D^2+1)).mpr
      nlinarith
    nlinarith only [hE]
  intro φ hφ hc hs hnn
  have H := setIntegral_second_deriv_le_of_local_differences (hFc.comp hσr)
    (show Continuous (fun t => D^2*G (evalReal σ t)) from continuous_const.mul (hGc.comp hσr)) hlocal
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hc hs hnn
  change (∫ t in Icc (0:ℝ) 1,F (evalReal σ t)*deriv (deriv φ) t) ≤
    D^2*(∫ t in Icc (0:ℝ) 1,G (evalReal σ t)*φ t)
  convert H using 1
  · rfl
  · simp_rw [mul_assoc]
    rw [integral_const_mul]
end WeakHessian

end
end

end OAI
