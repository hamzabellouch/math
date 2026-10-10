import Mathlib
import OAI.Analysis.AffineBernstein.LocalMaximumHessian
import OAI.Analysis.AffineBernstein.DualDetBarrier

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DualDetBound

lemma dualDetBarrier_peak_trace_algebra {N T P R v γ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hv : v < 0) (hγ : 0 < γ) (hRP : R ≤ T * P) (hγP : γ*P ≤ 1/2)
    (hpeak : γ*T - ((N+1)/(N+2))*γ^2*R + (N*(N+2)-γ*N*P)/v ≤ 0) :
    (-v)*T ≤ 2*N*(N+2)/γ := by
  have hden : 0 < N+2 := by linarith
  have ha : 0 ≤ (N+1)/(N+2) := by positivity
  have ha1 : (N+1)/(N+2) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hc : 0 ≤ ((N+1)/(N+2))*γ^2 := by positivity
  have hsmall : ((N+1)/(N+2))*γ^2*P ≤ γ/2 := by
    calc
      _ = ((N+1)/(N+2))*γ*(γ*P) := by ring
      _ ≤ ((N+1)/(N+2))*γ*(1/2) := mul_le_mul_of_nonneg_left hγP (by positivity)
      _ ≤ γ/2 := by nlinarith [mul_le_mul_of_nonneg_right ha1 hγ.le]
  have hex : ((N+1)/(N+2))*γ^2*R ≤ T*(γ/2) := by
    calc
      _ ≤ ((N+1)/(N+2))*γ^2*(T*P) := mul_le_mul_of_nonneg_left hRP hc
      _ = T*(((N+1)/(N+2))*γ^2*P) := by ring
      _ ≤ T*(γ/2) := mul_le_mul_of_nonneg_left hsmall hT
  have hdrop : γ*N*P/v ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hv.le
  have hm : γ*T/2 + N*(N+2)/v ≤ 0 := by rw [sub_div] at hpeak; linarith
  have hprod := mul_le_mul_of_nonneg_left hm (le_of_lt (neg_pos.mpr hv))
  have hv0 : v ≠ 0 := ne_of_lt hv
  have hsimp : (-v)*(γ*T/2 + N*(N+2)/v) = (-v)*γ*T/2 - N*(N+2) := by field_simp; ring
  rw [hsimp,mul_zero] at hprod
  apply (le_div_iff₀ hγ).mpr
  nlinarith

lemma dualDetBarrier_peak_trace_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ * positionSquared x ≤ 1/2)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    (-dualCutoff u h x) * (hessian u x)⁻¹.trace ≤ 2*(n:ℝ)*((n:ℝ)+2)/γ := by
  have hb := (contDiffOn_dualDetBarrier hΩ hu hp h ((n:ℝ)+2) γ hneg).contDiffAt
    (hΩ.mem_nhds hx)
  have hnon := inverseHessianTrace_nonpos_of_localMax hb (hp x hx) hmax
  rw [dualDetBarrier_peak_identity hΩ hu hp hm h hneg hx γ hmax] at hnon
  have ht : 0 ≤ (hessian u x)⁻¹.trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.inv.diag_nonneg)
  exact dualDetBarrier_peak_trace_algebra (Nat.cast_nonneg n) ht
    (Finset.sum_nonneg (fun coordinate _ => sq_nonneg (x coordinate)))
    (hneg x hx) hγ (inverseHessianPair_position_le_trace (hp x hx)) hsmall hnon

end DualDetBound


end
end AffineBernstein
end

end OAI
