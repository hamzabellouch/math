import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroPenalty
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LocalZeroCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

noncomputable def wideDirichletDiskPoint (t : ℝ) (w : ℂ) : ℂ := dirichletCenter t + (29/10 : ℂ)*w
noncomputable def wideNormalizedDirichlet {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w) /
    DirichletCharacter.LFunction chi (dirichletCenter t)
noncomputable def wideDirichletDiskEnvelope (q : ℕ) (t : ℝ) : ℝ :=
  10 * absoluteZetaTwo * (|t|+6) * (q : ℝ)

@[simp] theorem wideDirichletDiskPoint_re (t : ℝ) (w : ℂ) :
    (wideDirichletDiskPoint t w).re = 3 + (29/10:ℝ)*w.re := by
  simp [wideDirichletDiskPoint]

theorem wideDirichletDiskPoint_half_strip (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1/10 ≤ (wideDirichletDiskPoint t w).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  rw [wideDirichletDiskPoint_re]
  linarith

theorem wideDirichletDiskPoint_norm (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖wideDirichletDiskPoint t w‖ ≤ |t|+6 := by
  have hc : ‖dirichletCenter t‖ ≤ 3+|t| := by
    simpa [dirichletCenter, norm_mul] using
      (norm_add_le (3 : ℂ) ((t : ℂ)*Complex.I))
  have h := norm_add_le (dirichletCenter t) ((29/10 : ℂ)*w)
  have hn : ‖(29/10:ℂ)*w‖ = (29/10:ℝ)*‖w‖ := by rw [norm_mul]; norm_num
  rw [hn] at h
  change ‖wideDirichletDiskPoint t w‖ ≤ _ at h
  linarith

theorem wideNormalizedDirichlet_zero {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : wideNormalizedDirichlet chi t 0 = 1 := by
  unfold wideNormalizedDirichlet wideDirichletDiskPoint
  simp only [mul_zero, add_zero]
  exact div_self (LFunction_ne_zero_right chi (by simp))

theorem wideNormalizedDirichlet_analytic {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ) :
    AnalyticAt ℂ (wideNormalizedDirichlet chi t) w := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hd : Differentiable ℂ (wideNormalizedDirichlet chi t) := by
    unfold wideNormalizedDirichlet wideDirichletDiskPoint
    fun_prop
  exact hd.analyticAt w

theorem wideNormalizedDirichlet_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖wideNormalizedDirichlet chi t w‖ ≤ wideDirichletDiskEnvelope q t := by
  have hs := wideDirichletDiskPoint_half_strip t hw
  have hu0 := norm_LFunction_le_partial_sum_bound chi hchi (by linarith :
    0 < (wideDirichletDiskPoint t w).re)
  have hu : ‖DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w)‖ ≤
      10 * ‖wideDirichletDiskPoint t w‖ * (q : ℝ) := by
    apply hu0.trans
    apply (div_le_iff₀ (by linarith : 0 < (wideDirichletDiskPoint t w).re)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) by positivity)
      (norm_nonneg (wideDirichletDiskPoint t w))]

  have hi := norm_inv_LFunction_le_absoluteZetaTwo chi (s := dirichletCenter t) (by norm_num)
  have hZ : 0 ≤ absoluteZetaTwo := zero_le_one.trans one_le_absoluteZetaTwo
  unfold wideNormalizedDirichlet
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (10 * ‖wideDirichletDiskPoint t w‖ * (q : ℝ)) * absoluteZetaTwo :=
      mul_le_mul hu hi (norm_nonneg _) (by positivity)
    _ ≤ (10 * (|t|+6) * (q : ℝ)) * absoluteZetaTwo := by
      gcongr
      exact wideDirichletDiskPoint_norm t hw
    _ = wideDirichletDiskEnvelope q t := by unfold wideDirichletDiskEnvelope; ring

theorem wideDirichletDiskEnvelope_gt_one (q : ℕ) [NeZero q] (t : ℝ) :
    1 < wideDirichletDiskEnvelope q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hZ := one_le_absoluteZetaTwo
  have ht := abs_nonneg t
  unfold wideDirichletDiskEnvelope
  have h1 : 60 ≤ 10 * absoluteZetaTwo * (|t|+6) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 10 * absoluteZetaTwo * (|t|+6))
  nlinarith

end Ostmann.Dirichlet

end OAI
