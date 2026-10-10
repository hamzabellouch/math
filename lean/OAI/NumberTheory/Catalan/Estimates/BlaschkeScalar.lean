import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set

namespace InternalCatalan

def blaschkeWeight (x : ℝ) : ℝ := (1 - x ^ 2) / (1 + x ^ 2)

private def blaschkeLogDefect (a t : ℝ) : ℝ :=
  Real.log (t + a) - Real.log (1 + a * t) -
    (1 - a) / (1 + a) * Real.log t

private theorem blaschkeLogDefect_hasDerivAt {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (blaschkeLogDefect a)
      (1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t) t := by
  have hn : t + a ≠ 0 := ne_of_gt (by positivity)
  have hd : 1 + a * t ≠ 0 := ne_of_gt (by positivity)
  have h := ((((hasDerivAt_id t).add_const a).log hn).sub
      ((((hasDerivAt_id t).const_mul a).const_add 1).log hd)).sub
      ((Real.hasDerivAt_log ht.ne').const_mul ((1 - a) / (1 + a)))
  simp only [id_eq, mul_one] at h
  change HasDerivAt (fun y : ℝ => Real.log (y + a) - Real.log (1 + a * y) -
      ((1 - a) / (1 + a)) * Real.log y)
    (1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) * t⁻¹) t at h
  change HasDerivAt (fun y : ℝ => Real.log (y + a) - Real.log (1 + a * y) -
      ((1 - a) / (1 + a)) * Real.log y) _ t
  simpa only [div_eq_mul_inv] using h

theorem blaschke_log_derivative_nonpos {a t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) :
    1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t ≤ 0 := by
  have hta : t + a ≠ 0 := ne_of_gt (by positivity)
  have hat : 1 + a * t ≠ 0 := ne_of_gt (by positivity)
  have ha' : 1 + a ≠ 0 := ne_of_gt (by positivity)
  have hid :
      1 / (t + a) - a / (1 + a * t) - ((1 - a) / (1 + a)) / t =
      -(a * (1 - a) * (t - 1) ^ 2) / ((t + a) * (1 + a * t) * (1 + a) * t) := by
    field_simp [hta, hat, ha', ht.ne']
    ring
  rw [hid]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg _))
  · positivity

theorem blaschke_log_ratio_lower {a t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    (1 - a) / (1 + a) * Real.log t ≤
      Real.log (t + a) - Real.log (1 + a * t) := by
  have hanti : AntitoneOn (blaschkeLogDefect a) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro y hy
      exact (blaschkeLogDefect_hasDerivAt ha hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (blaschkeLogDefect_hasDerivAt ha (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(blaschkeLogDefect_hasDerivAt ha (interior_subset hy)).deriv]
      exact blaschke_log_derivative_nonpos ha ha1 (interior_subset hy)
  have h := hanti ht (show (1 : ℝ) ∈ Ioi 0 by norm_num) ht1
  dsimp only [blaschkeLogDefect] at h
  simp only [mul_one, Real.log_one, mul_zero, add_comm 1 a, sub_self] at h
  rw [add_comm a 1] at h
  linarith

theorem blaschke_factor_log_lower {x u : ℝ}
    (hx : x ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    blaschkeWeight x * Real.log u ≤
      (Real.log (u ^ 2 + x ^ 2) - Real.log (1 + x ^ 2 * u ^ 2)) / 2 := by
  have h := blaschke_log_ratio_lower (sq_nonneg x) hx (sq_pos_of_pos hu)
    (show u ^ 2 ≤ 1 by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)])
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  dsimp only [blaschkeWeight]
  nlinarith

end InternalCatalan

end

end OAI
