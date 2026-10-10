import Mathlib
import OAI.Analysis.AffineBernstein.DetBarrierPhase
import OAI.Analysis.AffineBernstein.DualDetBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetPhase

/-- The pullback of the dual determinant phase to primal coordinates. -/
def dualDetPhase {n : ℕ} (u : Space n → ℝ) (h γ : ℝ) (x : Space n) : ℝ :=
  ((hessian u x).det)⁻¹ * (-dualCutoff u h x)^(n+2) * Real.exp (γ * positionEnergy x)

lemma dualDetPhase_eq_exp {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) {h : ℝ} (hn : dualCutoff u h x < 0) (γ : ℝ) :
    dualDetPhase u h γ x = Real.exp (dualDetBarrier u h ((n:ℝ)+2) γ x) := by
  unfold dualDetPhase dualDetBarrier logHessianDet
  rw [Real.exp_add,Real.exp_add,neg_one_mul,Real.exp_neg,Real.exp_log hp.det_pos]
  rw [← Real.log_neg_eq_log (dualCutoff u h x)]
  congr 2
  have hh := Real.exp_nat_mul (Real.log (-dualCutoff u h x)) (n+2)
  rw [Real.exp_log (neg_pos.mpr hn)] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh.symm

lemma dualDetPhase_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) {h : ℝ} (hn : dualCutoff u h x < 0) (γ : ℝ) :
    0 < dualDetPhase u h γ x := by
  rw [dualDetPhase_eq_exp hp hn]
  exact Real.exp_pos _

lemma continuousOn_dualDetPhase {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (h γ : ℝ) :
    ContinuousOn (dualDetPhase u h γ) Ω := by
  have hh : ContinuousOn (fun x => (hessian u x).det) Ω := by
    intro x hx
    exact (contDiffAt_det_hessian (hu.contDiffAt (hΩ.mem_nhds hx))).continuousAt.continuousWithinAt
  exact (((hh.inv₀ (fun x hx => ne_of_gt (hp x hx).det_pos)).mul
    ((contDiffOn_dualCutoff hΩ hu h).continuousOn.neg.pow (n+2))).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul contDiff_positionEnergy.continuous.continuousOn)))

lemma dualDetPhase_peak_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω)
    {γ M D : ℝ} (hγ : 0 < γ) (_ : 0 ≤ M) (_ : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hrad : positionSquared x ≤ M) (hdepth : -dualCutoff u h x ≤ D)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    dualDetPhase u h γ x ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
  have hd : 0 < -dualCutoff u h x := neg_pos.mpr (hneg x hx)
  have ht : 0 ≤ (hessian u x)⁻¹.trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.inv.diag_nonneg)
  have hc : 0 ≤ 2*(n:ℝ)*((n:ℝ)+2)/γ := by positivity
  have hsm : γ * positionSquared x ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hrad hγ.le).trans hsmall
  have htrace := dualDetBarrier_peak_trace_bound hΩ hu hp hm h hneg hx hγ hsm hmax
  have hpow := pow_le_pow_left₀ (mul_nonneg hd.le ht) htrace n
  have hdet : ((hessian u x).det)⁻¹ ≤ (hessian u x)⁻¹.trace^n := by
    have H := posSemidef_det_le_trace_pow (hp x hx).posSemidef.inv
    simpa only [Matrix.det_nonsing_inv,Ring.inverse_eq_inv] using H
  have he : γ*positionEnergy x ≤ γ*M/2 := by
    change γ*((1/2)*positionSquared x) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hrad hγ.le]
  unfold dualDetPhase
  calc
    _ ≤ (hessian u x)⁻¹.trace^n * (-dualCutoff u h x)^(n+2) * Real.exp (γ*positionEnergy x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdet (by positivity)) (Real.exp_pos _).le
    _ = ((-dualCutoff u h x)*(hessian u x)⁻¹.trace)^n * (-dualCutoff u h x)^2 * Real.exp (γ*positionEnergy x) := by
      rw [pow_add,mul_pow]
      ring
    _ ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
      apply mul_le_mul
      · exact mul_le_mul hpow (pow_le_pow_left₀ hd.le hdepth 2) (sq_nonneg _) (pow_nonneg hc n)
      · exact Real.exp_le_exp.mpr he
      · exact (Real.exp_pos _).le
      · positivity

end DualDetPhase


end
end AffineBernstein
end

end OAI
