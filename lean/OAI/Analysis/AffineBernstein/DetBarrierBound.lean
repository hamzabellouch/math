import Mathlib
import OAI.Analysis.AffineBernstein.LocalMaximumHessian
import OAI.Analysis.AffineBernstein.PositiveMatrixTraceBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DetBarrierBound

lemma detBarrier_peak_trace_algebra {N T P Q R v γ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hv : v < 0) (hγ : 0 < γ) (hRP : R ≤ T * P) (hγP : γ*P ≤ 1/2)
    (hpeak : N*(N+2)/v^2*Q + γ*T - γ^2/(N+2)*R +
      (N*(N+2)+γ*N*P)/v ≤ 0) :
    (-v)*T ≤ 2*N*((N+2)/γ+P) := by
  have hden : 0 < N+2 := by linarith
  have hμ : 0 ≤ γ^2/(N+2) := by positivity
  have hfirst : 0 ≤ N*(N+2)/v^2*Q := by positivity
  have hsmall : γ^2/(N+2)*P ≤ γ/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hi : γ*(γ*P) ≤ γ*(1/2) := mul_le_mul_of_nonneg_left hγP hγ.le
    nlinarith [mul_nonneg hN hγ.le]
  have hex : γ^2/(N+2)*R ≤ T*(γ/2) := by
    calc
      _ ≤ γ^2/(N+2)*(T*P) := mul_le_mul_of_nonneg_left hRP hμ
      _ = T*(γ^2/(N+2)*P) := by ring
      _ ≤ T*(γ/2) := mul_le_mul_of_nonneg_left hsmall hT
  have hm : γ*T/2 + (N*(N+2)+γ*N*P)/v ≤ 0 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hm (le_of_lt (neg_pos.mpr hv))
  have hv0 : v ≠ 0 := ne_of_lt hv
  have hsimp : (-v)*(γ*T/2 + (N*(N+2)+γ*N*P)/v) =
      (-v)*γ*T/2 - (N*(N+2)+γ*N*P) := by field_simp [hv0]; ring
  rw [hsimp,mul_zero] at hprod
  apply (mul_le_mul_iff_right₀ hγ).mp
  calc
    γ*((-v)*T) ≤ 2*(N*(N+2)+γ*N*P) := by nlinarith
    _ = γ*(2*N*((N+2)/γ+P)) := by field_simp [ne_of_gt hγ]

lemma affineDetBarrier_peak_trace_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ * gradientSquared u x ≤ 1/2)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    (-u x) * (hessian u x).trace ≤
      2*(n:ℝ)*(((n:ℝ)+2)/γ+gradientSquared u x) := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hb := (contDiffOn_affineDetBarrier hΩ hu hp hneg ((n:ℝ)+2) γ).contDiffAt
    (hΩ.mem_nhds hx)
  have hnon := inverseHessianTrace_nonpos_of_localMax hb (hp x hx) hmax
  rw [affineDetBarrier_peak_identity hΩ hu hp hm hneg hx γ hmax] at hnon
  have ht : 0 ≤ (hessian u x).trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.diag_nonneg)
  exact detBarrier_peak_trace_algebra (Nat.cast_nonneg n) ht
    (gradientSquared_nonneg u x) (inverseHessianPair_self_nonneg (hp x hx) u)
    (hneg x hx) hγ (gradientHessianSquare_le_trace hu' (hp x hx)) hsmall hnon

end DetBarrierBound


end
end AffineBernstein
end

end OAI
