import OAI.GroupTheory.Thompson.AnalyticScalarProfiles
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-!
# Derivatives of the scalar displacement profiles

The one-sided derivatives are glued on the two closed/open half-lines.
In particular, the formulas below hold at all four transition points;
no transition point is removed from the domain.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace ThompsonNonamenability.Analytic

private theorem hasDerivAt_if_le_junction
    {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c)
    (hfg : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) d c := by
  have hleft : HasDerivWithinAt
      (fun t => if t ≤ c then f t else g t) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact ite_eq_left ht
    · simp
  have hright : HasDerivWithinAt
      (fun t => if t ≤ c then f t else g t) d (Ioi c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      exact ite_eq_right (not_le.mpr ht)
    · simpa using hfg
  simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hleft.union hright

private theorem hasDerivAt_if_le_all
    {f g df dg : ℝ → ℝ} (c : ℝ)
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (hfg : f c = g c) (hdfg : df c = dg c) (t : ℝ) :
    HasDerivAt (fun u => if u ≤ c then f u else g u)
      (if t ≤ c then df t else dg t) t := by
  rcases lt_trichotomy t c with ht | heq | ht
  · rw [ite_eq_left ht.le]
    apply (hf t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact ite_eq_left hu.le
  · subst t
    rw [ite_eq_left le_rfl]
    exact hasDerivAt_if_le_junction (hf c) ((hg c).congr_deriv hdfg.symm) hfg
  · rw [ite_eq_right (not_le.mpr ht)]
    apply (hg t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact ite_eq_right (not_le.mpr hu)

private theorem if_lt_eq_if_le
    {f g : ℝ → ℝ} {c : ℝ} (hfg : f c = g c) (t : ℝ) :
    (if t < c then f t else g t) = (if t ≤ c then f t else g t) := by
  rcases lt_trichotomy t c with ht | rfl | ht
  · simp [ht, ht.le]
  · simp [hfg]
  · simp [not_lt.mpr ht.le, not_le.mpr ht]

private theorem hasDerivAt_a_middle (t : ℝ) :
    HasDerivAt (fun u : ℝ => 5 / 16 - (3 - u) ^ 2 / 16) ((3 - t) / 8) t := by
  have h := ((((hasDerivAt_id' t).const_sub 3).fun_pow 2).div_const 16).const_sub
    (5 / 16 : ℝ)
  exact h.congr_deriv (by norm_num ; ring)

private theorem hasDerivAt_theta_middle (t : ℝ) :
    HasDerivAt (fun u : ℝ => (u - 1) ^ 2 / 2) (t - 1) t := by
  have h := (((hasDerivAt_id' t).sub_const 1).fun_pow 2).div_const 2
  exact h.congr_deriv (by norm_num)

/-- The radial scalar profile is differentiable at every real point,
including its two junctions. -/
theorem hasDerivAt_a (t : ℝ) : HasDerivAt a (aDeriv t) t := by
  have hm : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => if v ≤ 3 then 5 / 16 - (3 - v) ^ 2 / 16 else 5 / 16)
      (if u ≤ 3 then (3 - u) / 8 else 0) u :=
    hasDerivAt_if_le_all 3 hasDerivAt_a_middle
      (fun u => hasDerivAt_const u (5 / 16 : ℝ)) (by norm_num) (by norm_num)
  have h : HasDerivAt
      (fun u : ℝ => if u ≤ 2 then u / 8 else
        if u ≤ 3 then 5 / 16 - (3 - u) ^ 2 / 16 else 5 / 16)
      (if t ≤ 2 then 1 / 8 else if t ≤ 3 then (3 - t) / 8 else 0) t :=
    hasDerivAt_if_le_all 2 (fun u => (hasDerivAt_id u).div_const 8)
      hm (by norm_num) (by norm_num) t
  have hf : a = (fun u : ℝ => if u ≤ 2 then u / 8 else
      if u ≤ 3 then 5 / 16 - (3 - u) ^ 2 / 16 else 5 / 16) := by
    funext u
    by_cases hu : u ≤ 2
    · simp [a, hu]
    · simp only [a, ite_eq_right hu]
      exact if_lt_eq_if_le (f := fun v : ℝ => 5 / 16 - (3 - v) ^ 2 / 16)
        (g := fun _ : ℝ => 5 / 16) (c := 3) (by norm_num) u
  have hd : aDeriv t =
      (if t ≤ 2 then 1 / 8 else if t ≤ 3 then (3 - t) / 8 else 0) := by
    by_cases ht : t ≤ 2
    · simp [aDeriv, ht]
    · simp only [aDeriv, ite_eq_right ht]
      exact if_lt_eq_if_le (f := fun v : ℝ => (3 - v) / 8)
        (g := fun _ : ℝ => 0) (c := 3) (by norm_num) t
  rw [hf, hd]
  exact h

/-- The angular scalar profile is differentiable at every real point,
including its two junctions. -/
theorem hasDerivAt_theta (t : ℝ) : HasDerivAt theta (thetaDeriv t) t := by
  have hm : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => if v ≤ 2 then (v - 1) ^ 2 / 2 else v - 3 / 2)
      (if u ≤ 2 then u - 1 else 1) u :=
    hasDerivAt_if_le_all 2 hasDerivAt_theta_middle
      (fun u => (hasDerivAt_id u).sub_const (3 / 2 : ℝ))
      (by norm_num) (by norm_num)
  have h : HasDerivAt
      (fun u : ℝ => if u ≤ 1 then 0 else
        if u ≤ 2 then (u - 1) ^ 2 / 2 else u - 3 / 2)
      (if t ≤ 1 then 0 else if t ≤ 2 then t - 1 else 1) t :=
    hasDerivAt_if_le_all 1 (fun u => hasDerivAt_const u (0 : ℝ))
      hm (by norm_num) (by norm_num) t
  have hf : theta = (fun u : ℝ => if u ≤ 1 then 0 else
      if u ≤ 2 then (u - 1) ^ 2 / 2 else u - 3 / 2) := by
    funext u
    by_cases hu : u ≤ 1
    · simp [theta, hu]
    · simp only [theta, ite_eq_right hu]
      exact if_lt_eq_if_le (f := fun v : ℝ => (v - 1) ^ 2 / 2)
        (g := fun v : ℝ => v - 3 / 2) (c := 2) (by norm_num) u
  have hd : thetaDeriv t =
      (if t ≤ 1 then 0 else if t ≤ 2 then t - 1 else 1) := by
    by_cases ht : t ≤ 1
    · simp [thetaDeriv, ht]
    · simp only [thetaDeriv, ite_eq_right ht]
      exact if_lt_eq_if_le (f := fun v : ℝ => v - 1)
        (g := fun _ : ℝ => 1) (c := 2) (by norm_num) t
  rw [hf, hd]
  exact h

theorem deriv_a (t : ℝ) : deriv a t = aDeriv t := (hasDerivAt_a t).deriv

theorem deriv_theta (t : ℝ) : deriv theta t = thetaDeriv t := (hasDerivAt_theta t).deriv

theorem differentiable_a : Differentiable ℝ a := fun t => (hasDerivAt_a t).differentiableAt

theorem differentiable_theta : Differentiable ℝ theta :=
  fun t => (hasDerivAt_theta t).differentiableAt

theorem continuous_a : Continuous a := differentiable_a.continuous

theorem continuous_theta : Continuous theta := differentiable_theta.continuous

theorem continuous_aDeriv : Continuous aDeriv := aDeriv_lipschitz.continuous

theorem continuous_thetaDeriv : Continuous thetaDeriv := thetaDeriv_lipschitz.continuous

end ThompsonNonamenability.Analytic

end

end OAI
