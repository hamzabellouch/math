import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodSupport

namespace OAI

namespace ConvexSkorokhod

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem regulator_variation_bound (B : Body E) (x₀ c : E) (r R : ℝ)
    (_hx₀ : x₀∈B.carrier) (hr : 0<r) (hR : ‖x₀-c‖≤R)
    (hball : Metric.closedBall c r⊆B.carrier) (w : ℕ → E) (N : ℕ)
    (hw : ∀n≤N,‖w n-w 0‖≤r/2) :
    variation (regulator B x₀ w) N≤R^2/r := by
  let k := regulator B x₀ w
  have hk₀ : k 0=0 := regulator_zero B x₀ w
  have hstep (i : ℕ) (hi : i<N) :
      (r/2)*‖k (i+1)-k i‖≤ inner ℝ (k (i+1)-k i) (c-x₀)-inner ℝ (k (i+1)-k i) (k (i+1)) := by
    have hb := ball_normal_impulse B.carrier c (walk B x₀ w (i+1)) (k (i+1)-k i) r hr.le hball
      (regulator_normal B x₀ w i)
    have he : c-walk B x₀ w (i+1)=(c-x₀)-(w (i+1)-w 0)-k (i+1) := by dsimp [k,regulator];abel
    rw [he,inner_sub_right,inner_sub_right] at hb
    have hn := (abs_le.mp (abs_real_inner_le_norm (k (i+1)-k i) (w (i+1)-w 0))).1
    have ho := mul_le_mul_of_nonneg_left (hw (i+1) hi) (norm_nonneg (k (i+1)-k i))
    nlinarith
  have hs := Finset.sum_le_sum (fun i (hi : i∈Finset.range N) => hstep i (Finset.mem_range.mp hi))
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,sum_inner_increment,hk₀,sub_zero] at hs
  change r/2*variation k N≤ inner ℝ (k N) (c-x₀)-(∑i∈Finset.range N,inner ℝ (k (i+1)-k i) (k (i+1))) at hs
  have he := sum_inner_energy k N
  rw [hk₀,norm_zero,zero_pow (by norm_num : 2≠0),sub_zero] at he
  have hpos : 0≤∑i∈Finset.range N,‖k (i+1)-k i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc := (real_inner_le_norm (k N) (c-x₀)).trans (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hR) (norm_nonneg (k N)))
  apply (le_div_iff₀ hr).mpr
  nlinarith [sq_nonneg (‖k N‖-R)]

end ConvexSkorokhod

end OAI
