import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

/-! Stability and consistency for the kick-drift approximation of the
matrix Jacobi equation. The estimates use operator bounds, so no two
curvature matrices are required to commute. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def kick (R : E →L[ℝ] E) (h : ℝ) (x v : E) : E := v - h • R x

def drift (R : E →L[ℝ] E) (h : ℝ) (x v : E) : E := x + h • kick R h x v

/-- A first-order Taylor remainder with the uniform quadratic bound needed
for convergence. The slightly larger constant avoids unnecessary sharpness. -/
theorem first_order_remainder {f d : ℝ → E} {a h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hd : ∀ s ∈ Set.Icc a (a + h), HasDerivAt f (d s) s)
    (hlip : ∀ s ∈ Set.Icc a (a + h), ‖d s - d a‖ ≤ L * (s - a)) :
    ‖f (a + h) - f a - h • d a‖ ≤ L * h ^ 2 := by
  let g : ℝ → E := fun s => f s - f a - (s - a) • d a
  have hg (s : ℝ) (hs : s ∈ Set.Icc a (a + h)) :
      HasDerivAt g (d s - d a) s := by
    convert ((hd s hs).sub_const (f a)).sub
      (((hasDerivAt_id s).sub_const a).smul_const (d a)) using 1
    all_goals first | rfl | simp
  have hb (s : ℝ) (hs : s ∈ Set.Ico a (a + h)) : ‖d s - d a‖ ≤ L * h :=
    (hlip s ⟨hs.1, hs.2.le⟩).trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hL)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hg s hs).hasDerivWithinAt) hb (a + h) ⟨by linarith, le_rfl⟩
  simpa [g, pow_two, mul_assoc] using h

theorem kick_stability {R : E →L[ℝ] E} {h K : ℝ}
    (hh : 0 ≤ h) (hR : ‖R‖ ≤ K) (x v y w : E) :
    ‖kick R h x v - kick R h y w‖ ≤ ‖v - w‖ + h * K * ‖x - y‖ := by
  have hid : kick R h x v - kick R h y w = (v - w) - h • R (x - y) := by
    simp only [kick, map_sub, smul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖v - w‖ + ‖h • R (x - y)‖ := norm_sub_le _ _
    _ = ‖v - w‖ + h * ‖R (x - y)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ ‖v - w‖ + h * (K * ‖x - y‖) := by
      gcongr
      exact (R.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
    _ = _ := by ring

theorem kick_drift_stability {R : E →L[ℝ] E} {h K : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hR : ‖R‖ ≤ K)
    (x v y w : E) :
    ‖drift R h x v - drift R h y w‖ + ‖kick R h x v - kick R h y w‖ ≤
      (1 + (1 + 2 * K) * h) * (‖x - y‖ + ‖v - w‖) := by
  have hv := kick_stability hh hR x v y w
  have hx : ‖drift R h x v - drift R h y w‖ ≤
      ‖x - y‖ + h * ‖kick R h x v - kick R h y w‖ := by
    have hid : drift R h x v - drift R h y w =
        (x - y) + h • (kick R h x v - kick R h y w) := by
      simp only [drift, smul_sub]
      abel
    rw [hid]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] using norm_add_le
      (x - y) (h • (kick R h x v - kick R h y w))
  have hbound : h * K * ‖x - y‖ * (1 - h) +
      h * ‖x - y‖ + 2 * K * h * ‖v - w‖ ≥ 0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hv hh]

/-- Local error of the actual update, from the two Taylor remainders. -/
theorem kick_drift_local_error {R : E →L[ℝ] E} {h Cx Cv F : ℝ}
    {x v x' v' : E} (hh : 0 ≤ h)
    (hx : ‖x' - x - h • v‖ ≤ Cx * h ^ 2)
    (hv : ‖v' - v + h • R x‖ ≤ Cv * h ^ 2)
    (hforce : ‖R x‖ ≤ F) :
    ‖x' - drift R h x v‖ + ‖v' - kick R h x v‖ ≤
      (Cx + Cv + F) * h ^ 2 := by
  have hvid : v' - kick R h x v = v' - v + h • R x := by unfold kick; abel
  have hxid : x' - drift R h x v = (x' - x - h • v) + (h * h) • R x := by
    simp only [drift, kick, smul_sub, smul_smul]
    abel
  have hxbound : ‖x' - drift R h x v‖ ≤ (Cx + F) * h ^ 2 := by
    rw [hxid]
    calc
      _ ≤ ‖x' - x - h • v‖ + ‖(h * h) • R x‖ := norm_add_le _ _
      _ = ‖x' - x - h • v‖ + h ^ 2 * ‖R x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh hh), pow_two]
      _ ≤ Cx * h ^ 2 + h ^ 2 * F := add_le_add hx (mul_le_mul_of_nonneg_left hforce (sq_nonneg h))
      _ = _ := by ring
  rw [hvid]
  linarith

/-- The local error hypotheses follow from the differential equation and
Lipschitz bounds for its velocity and acceleration on the current interval. -/
theorem kick_drift_consistency {R : ℝ → E →L[ℝ] E} {X V : ℝ → E}
    {a h Lx Lv F : ℝ} (hh : 0 ≤ h) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hX : ∀ s ∈ Set.Icc a (a + h), HasDerivAt X (V s) s)
    (hV : ∀ s ∈ Set.Icc a (a + h), HasDerivAt V (-(R s) (X s)) s)
    (hvelocity : ∀ s ∈ Set.Icc a (a + h), ‖V s - V a‖ ≤ Lx * (s - a))
    (hacceleration : ∀ s ∈ Set.Icc a (a + h),
      ‖-(R s) (X s) - -(R a) (X a)‖ ≤ Lv * (s - a))
    (hforce : ‖(R a) (X a)‖ ≤ F) :
    ‖X (a + h) - drift (R a) h (X a) (V a)‖ +
      ‖V (a + h) - kick (R a) h (X a) (V a)‖ ≤ (Lx + Lv + F) * h ^ 2 := by
  have hx := first_order_remainder hh hLx hX hvelocity
  have hv := first_order_remainder hh hLv hV hacceleration
  apply kick_drift_local_error hh hx ?_ hforce
  simpa only [smul_neg, sub_neg_eq_add] using hv

/-- Discrete Grönwall on precisely the finite interval used by the Jacobi
approximation. It also handles zero step size and zero local error. -/
theorem finite_error_bound {u : ℕ → ℝ} {N : ℕ} {h K C : ℝ}
    (hh : 0 ≤ h) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hu0 : u 0 = 0) (hu : ∀ i ≤ N, 0 ≤ u i)
    (hstep : ∀ i < N, u (i + 1) ≤ (1 + K * h) * u i + C * h ^ 2) :
    u N ≤ C * N * h ^ 2 * Real.exp (K * N * h) := by
  let U : ℕ → ℝ := fun i => u (min i N)
  have hU (i : ℕ) (_ : 0 ≤ i) : U (i + 1) ≤ (1 + K * h) * U i + C * h ^ 2 := by
    by_cases hi : i < N
    · simpa [U, min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)] using hstep i hi
    · have hN : N ≤ i := Nat.le_of_not_gt hi
      simp only [U, min_eq_right hN, min_eq_right (hN.trans (Nat.le_succ i))]
      have hhprod : 0 ≤ K * h * u N := mul_nonneg (mul_nonneg hK hh) (hu N le_rfl)
      have hlocal : 0 ≤ C * h ^ 2 := mul_nonneg hC (sq_nonneg h)
      nlinarith
  have hb := discrete_gronwall (show 0 ≤ U 0 by simp [U, hu0]) hU
    (fun _ _ => mul_nonneg hK hh) (fun _ _ => mul_nonneg hC (sq_nonneg h))
    (show 0 ≤ N by omega)
  simp [U, hu0, Finset.sum_const] at hb
  have he : (N : ℝ) * (K * h) = K * N * h := by ring
  rw [he] at hb
  convert hb using 1
  ring

theorem finite_error_bound_scaled {u : ℕ → ℝ} {N : ℕ} {t K C : ℝ}
    (hN : 0 < N) (ht : 0 ≤ t) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hu0 : u 0 = 0) (hu : ∀ i ≤ N, 0 ≤ u i)
    (hstep : ∀ i < N, u (i + 1) ≤
      (1 + K * (t / N)) * u i + C * (t / N) ^ 2) :
    u N ≤ (C * t ^ 2 * Real.exp (K * t)) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := finite_error_bound (div_nonneg ht (Nat.cast_nonneg N)) hK hC hu0 hu hstep
  convert hb using 1
  field_simp

/-- Propagation of local Jacobi errors, with the curvature operator allowed
to vary arbitrarily from one mesh point to the next. -/
theorem kick_drift_global_error
    {R : ℕ → E →L[ℝ] E} {x v X V : ℕ → E} {N : ℕ} {h K C : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hR : ∀ i < N, ‖R i‖ ≤ K)
    (hx0 : x 0 = X 0) (hv0 : v 0 = V 0)
    (hxstep : ∀ i < N, x (i + 1) = drift (R i) h (x i) (v i))
    (hvstep : ∀ i < N, v (i + 1) = kick (R i) h (x i) (v i))
    (hlocal : ∀ i < N,
      ‖X (i + 1) - drift (R i) h (X i) (V i)‖ +
      ‖V (i + 1) - kick (R i) h (X i) (V i)‖ ≤ C * h ^ 2) :
    ‖x N - X N‖ + ‖v N - V N‖ ≤
      C * N * h ^ 2 * Real.exp ((1 + 2 * K) * N * h) := by
  let u : ℕ → ℝ := fun i => ‖x i - X i‖ + ‖v i - V i‖
  apply finite_error_bound hh (by positivity) hC (u := u)
  · simp [u, hx0, hv0]
  · intro i _
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro i hi
    have hstab := kick_drift_stability hh hh1 hK (hR i hi) (x i) (v i) (X i) (V i)
    have hpos := norm_sub_le_norm_sub_add_norm_sub
      (drift (R i) h (x i) (v i)) (drift (R i) h (X i) (V i)) (X (i + 1))
    have hvel := norm_sub_le_norm_sub_add_norm_sub
      (kick (R i) h (x i) (v i)) (kick (R i) h (X i) (V i)) (V (i + 1))
    rw [norm_sub_rev (drift (R i) h (X i) (V i)) (X (i + 1))] at hpos
    rw [norm_sub_rev (kick (R i) h (X i) (V i)) (V (i + 1))] at hvel
    dsimp only [u]
    rw [hxstep i hi, hvstep i hi]
    linarith [hlocal i hi]

/-- The global estimate on a mesh of fixed total length has order `1/N`. -/
theorem kick_drift_global_error_scaled
    {R : ℕ → E →L[ℝ] E} {x v X V : ℕ → E} {N : ℕ} {t K C : ℝ}
    (hN : 0 < N) (ht : 0 ≤ t) (hmesh : t / N ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : ∀ i < N, ‖R i‖ ≤ K)
    (hx0 : x 0 = X 0) (hv0 : v 0 = V 0)
    (hxstep : ∀ i < N, x (i + 1) = drift (R i) (t / N) (x i) (v i))
    (hvstep : ∀ i < N, v (i + 1) = kick (R i) (t / N) (x i) (v i))
    (hlocal : ∀ i < N,
      ‖X (i + 1) - drift (R i) (t / N) (X i) (V i)‖ +
      ‖V (i + 1) - kick (R i) (t / N) (X i) (V i)‖ ≤ C * (t / N) ^ 2) :
    ‖x N - X N‖ + ‖v N - V N‖ ≤
      (C * t ^ 2 * Real.exp ((1 + 2 * K) * t)) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := kick_drift_global_error (div_nonneg ht (Nat.cast_nonneg N)) hmesh
    hK hC hR hx0 hv0 hxstep hvstep hlocal
  have he : (1 + 2 * K) * N * (t / N) = (1 + 2 * K) * t := by
    field_simp
  rw [he] at hb
  convert hb using 1
  field_simp

omit [NormedSpace ℝ E] in
/-- Position and backward velocity both converge once the uniform mesh
estimate is available. This applies to matrices as a finite-dimensional
normed space, without any commutation assumption. -/
theorem converges_of_inverse_mesh_error
    {x v : ℕ → E} {X V : E} {C : ℝ}
    (herror : ∀ᶠ N in atTop,
      ‖x N - X‖ + ‖v N - V‖ ≤ C / N) :
    Tendsto x atTop (nhds X) ∧ Tendsto v atTop (nhds V) := by
  have hsum : Tendsto (fun N => ‖x N - X‖ + ‖v N - V‖) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => by positivity) herror
      (tendsto_const_div_atTop_nhds_zero_nat C)
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun _ => le_add_of_nonneg_right
      (norm_nonneg _)) hsum
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun _ => le_add_of_nonneg_left
      (norm_nonneg _)) hsum

end

end PositiveEinsteinFour.Jacobi

end OAI
