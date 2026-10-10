import Mathlib
import OAI.Analysis.AffineBernstein.DetBarrierBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DetBarrierPhase

lemma posSemidef_det_le_trace_pow {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : A.det ≤ A.trace ^ n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues,hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    _ ≤ ∏ _i : Fin n, (∑ j, hA.isHermitian.eigenvalues j) := by
      apply Finset.prod_le_prod₀
      · intro index _
        exact hA.eigenvalues_nonneg index
      · intro index hindex
        exact Finset.single_le_sum (fun entry _ => hA.eigenvalues_nonneg entry) hindex
    _ = _ := by simp

/-- Continuous phase whose logarithm is the maximum-principle barrier on a
negative section; the phase vanishes, rather than diverging, on its boundary. -/
def affineDetPhase {n : ℕ} (u : Space n → ℝ) (γ : ℝ) (x : Space n) : ℝ :=
  (hessian u x).det * (-u x)^(n+2) * Real.exp (γ * gradientEnergy u x)

lemma affineDetPhase_eq_exp {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) (γ : ℝ) :
    affineDetPhase u γ x = Real.exp (affineDetBarrier u ((n:ℝ)+2) γ x) := by
  unfold affineDetPhase affineDetBarrier logHessianDet
  rw [Real.exp_add,Real.exp_add,Real.exp_log hp.det_pos]
  rw [← Real.log_neg_eq_log (u x)]
  congr 2
  have hh := Real.exp_nat_mul (Real.log (-u x)) (n+2)
  rw [Real.exp_log (neg_pos.mpr hn)] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh.symm

lemma affineDetPhase_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) (γ : ℝ) :
    0 < affineDetPhase u γ x := by
  rw [affineDetPhase_eq_exp hp hn]
  exact Real.exp_pos _

lemma continuousOn_affineDetPhase {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (γ : ℝ) :
    ContinuousOn (affineDetPhase u γ) Ω := by
  have hh : ContinuousOn (fun x => (hessian u x).det) Ω := by
    intro x hx
    exact (contDiffAt_det_hessian (hu.contDiffAt (hΩ.mem_nhds hx))).continuousAt.continuousWithinAt
  exact ((hh.mul (hu.continuousOn.neg.pow (n+2))).mul
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (contDiffOn_gradientEnergy hΩ hu).continuousOn)))

lemma affineDetPhase_peak_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hgrad : gradientSquared u x ≤ M) (hdepth : -u x ≤ D)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    affineDetPhase u γ x ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
  have hd : 0 < -u x := neg_pos.mpr (hneg x hx)
  have ht : 0 ≤ (hessian u x).trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun i hi => (hp x hx).posSemidef.diag_nonneg)
  have hc : 0 ≤ 2*(n:ℝ)*(((n:ℝ)+2)/γ+M) := by positivity
  have hsm : γ * gradientSquared u x ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hgrad hγ.le).trans hsmall
  have htrace := affineDetBarrier_peak_trace_bound hΩ hu hp hm hneg hx hγ hsm hmax
  have htrace' : (-u x)*(hessian u x).trace ≤ 2*(n:ℝ)*(((n:ℝ)+2)/γ+M) :=
    htrace.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hgrad) (by positivity))
  have hpow : ((-u x)*(hessian u x).trace)^n ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n :=
    pow_le_pow_left₀ (mul_nonneg hd.le ht) htrace' n
  have hdet := posSemidef_det_le_trace_pow (hp x hx).posSemidef
  have he : γ*gradientEnergy u x ≤ γ*M/2 := by
    change γ*((1/2)*gradientSquared u x) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hgrad hγ.le]
  unfold affineDetPhase
  calc
    _ ≤ (hessian u x).trace^n * (-u x)^(n+2) * Real.exp (γ*gradientEnergy u x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdet (by positivity)) (Real.exp_pos _).le
    _ = ((-u x)*(hessian u x).trace)^n * (-u x)^2 * Real.exp (γ*gradientEnergy u x) := by
      rw [pow_add,mul_pow]
      ring
    _ ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
      apply mul_le_mul
      · exact mul_le_mul hpow ((sq_le_sq₀ hd.le hD).mpr hdepth) (sq_nonneg _) (pow_nonneg hc n)
      · exact Real.exp_le_exp.mpr he
      · exact (Real.exp_pos _).le
      · positivity

end DetBarrierPhase


end
end AffineBernstein
end

end OAI
