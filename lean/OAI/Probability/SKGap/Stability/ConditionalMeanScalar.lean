import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Real
lemma conditional_perp_mean_scalar {N q s : ℝ} (hN : 0 < N) (hq : 0 < q) (hs : 0 < s)
    (j a B w u : ℝ) :
    (j/N*sqrt (N*q)/s)*(w+B*sqrt (N*q)*u-(N*(a+B*q)/sqrt (N*q))*u)=
      j*sqrt (q/s)*(w/(sqrt N*sqrt s))-j*a/s*u := by
  have hn := (sqrt_pos.mpr hN).ne'
  have hq' := (sqrt_pos.mpr hq).ne'
  have hs' := (sqrt_pos.mpr hs).ne'
  rw [sqrt_mul hN.le,sqrt_div hq.le]
  field_simp
  ring_nf
  simp only [sq_sqrt hN.le,sq_sqrt hq.le,sq_sqrt hs.le]
  have hcube : sqrt N^3=N*sqrt N := by
    linear_combination sqrt N*(sq_sqrt hN.le)
  rw [hcube]
  ring

lemma conditional_parallel_mean_scalar {N q S : ℝ} (hN : 0 < N) (hq : 0 < q)
    (j a B : ℝ) :
    (2*(j/N)*sqrt (N*q)/S)*((N*(a+B*q))/sqrt (N*q))=2*j*(a+B*q)/S := by
  have hc : sqrt (N*q) ≠ 0 := (sqrt_pos.mpr (mul_pos hN hq)).ne'
  by_cases hS : S=0
  · simp [hS]
  · field_simp

end SKGap
end
end

end OAI
