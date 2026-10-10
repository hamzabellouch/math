import OAI.MeasureTheory.Falconer.Geometry.ChartCoordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-!
# The fixed quadratic chart at a sphere pole

This is the actual chart in `osc:stationary`. Its phase is exactly quadratic,
in every dimension. Surface measure transport and its Jacobian are separate
from the geometric statements here.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def quadraticSpherePoint {n : ℕ} (u : Space n) : Space (n+1) :=
  coordinateJoin (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)

@[simp] theorem quadraticSpherePoint_zero_coord {n : ℕ} (u : Space n) :
    quadraticSpherePoint u 0 = 1-‖u‖^2/2 := by
  simp [quadraticSpherePoint, coordinateJoin_eq]

@[simp] theorem quadraticSpherePoint_succ_coord {n : ℕ} (u : Space n) (i : Fin n) :
    quadraticSpherePoint u i.succ = Real.sqrt (1-‖u‖^2/4) * u i := by
  simp [quadraticSpherePoint, coordinateJoin_eq]

theorem quadraticSpherePoint_norm {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u‖ = 1 := by
  have hu2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have harg : 0 ≤ 1-‖u‖^2/4 := by nlinarith
  have hs := Real.sq_sqrt harg
  have he := coordinateJoin_norm_sq (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs] at he
  change ‖quadraticSpherePoint u‖^2 = _ at he
  nlinarith [norm_nonneg (quadraticSpherePoint u)]

noncomputable def quadraticSphereChart {n : ℕ} (u : Metric.ball (0 : Space n) 1) :
    Sphere (n+1) :=
  ⟨quadraticSpherePoint u, by
    rw [Metric.mem_sphere, dist_zero_right]
    have hu : ‖(u : Space n)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using u.property
    exact quadraticSpherePoint_norm (hu.le.trans (by norm_num))⟩

/-- The oscillatory phase at the pole is exactly `1 - ‖u‖²/2`. -/
theorem quadraticSpherePoint_phase {n : ℕ} (u : Space n) :
    inner ℝ (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1) =
      1-‖u‖^2/2 := by
  simp [quadraticSpherePoint, coordinateJoin_inner]

theorem quadraticSpherePoint_contDiffAt {n : ℕ} {u : Space n} (hu : ‖u‖ < 2) :
    ContDiffAt ℝ ∞ (@quadraticSpherePoint n) u := by
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 2)).mpr hu
  have harg : 0 < 1-‖u‖^2/4 := by nlinarith
  have hs : ContDiffAt ℝ ∞ (fun v : Space n => Real.sqrt (1-‖v‖^2/4)) u :=
    (contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt harg.ne'
  apply (contDiffAt_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [quadraticSpherePoint_zero_coord] using
      (contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 2))
  · simpa only [quadraticSpherePoint_succ_coord] using
      hs.mul (contDiffAt_piLp_apply (p := 2) (i := j))

theorem quadraticSphereChart_mem_hemisphere {n : ℕ}
    (u : Metric.ball (0 : Space n) 1) : quadraticSphereChart u ∈ northHemisphere n := by
  change 0 < quadraticSpherePoint (u : Space n) 0
  rw [quadraticSpherePoint_zero_coord]
  have hu : ‖(u : Space n)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using u.property
  have hu2 := (sq_lt_sq₀ (norm_nonneg (u : Space n)) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  nlinarith

/-- The exact change from quadratic coordinates to the existing gnomonic
coordinates. On the unit ball its denominator is bounded away from zero. -/
noncomputable def quadraticToGnomonic {n : ℕ} (u : Space n) : Space n :=
  (Real.sqrt (1-‖u‖^2/4) / (1-‖u‖^2/2)) • u

theorem gnomonicChart_quadraticToGnomonic {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (gnomonicChart (quadraticToGnomonic u) : Space (n+1)) = quadraticSpherePoint u := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; nlinarith
  have he : northLift (quadraticToGnomonic u) = a⁻¹ • quadraticSpherePoint u := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [northLift_zero, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_zero_coord]
      change 1 = a⁻¹ * a
      exact (inv_mul_cancel₀ ha.ne').symm
    · simp only [northLift_succ, quadraticToGnomonic, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_succ_coord]
      dsimp only [a]
      ring
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    rw [he, norm_smul, quadraticSpherePoint_norm (hu.le.trans (by norm_num)),
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_one]
  change ‖northLift (quadraticToGnomonic u)‖⁻¹ • northLift (quadraticToGnomonic u) = _
  rw [hn, he, smul_smul, inv_inv, mul_inv_cancel₀ ha.ne', one_smul]

theorem quadraticToGnomonic_injOn (n : ℕ) :
    Set.InjOn (@quadraticToGnomonic n) (Metric.ball (0 : Space n) 1) := by
  intro u hu v hv heq
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hv' : ‖v‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hp : quadraticSpherePoint u = quadraticSpherePoint v := by
    rw [← gnomonicChart_quadraticToGnomonic hu',
      ← gnomonicChart_quadraticToGnomonic hv', heq]
  have hzero := congrArg (fun z : Space (n+1) => z 0) hp
  simp only [quadraticSpherePoint_zero_coord] at hzero
  have hs : ‖u‖^2 = ‖v‖^2 := by linarith
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu'
  have hq : Real.sqrt (1-‖u‖^2/4) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Space (n+1) => z i.succ) hp
  simp only [quadraticSpherePoint_succ_coord, ← hs] at hi
  exact mul_left_cancel₀ hq hi

end Falconer

end OAI
