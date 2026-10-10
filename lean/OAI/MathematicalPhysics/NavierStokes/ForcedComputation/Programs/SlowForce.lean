import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ForceGerm
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BoundedProfiles

namespace OAI

/-! The globally smooth slowdown has the calculated residual on a neighborhood
of nonnegative time, so its actual force inherits every derivative estimate. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
open ShearFlows

namespace ForcedComputation

theorem slowFromRest_eq_near_nonnegative {V : Velocity}
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    {t : ℝ} (ht : -(1 / 2 : ℝ) < t) (x : Space) :
    slowFromRest V (t, x) = slowVelocity V (t, x) := by
  by_cases hn : t ≤ 0
  · have hp : 0 < 1 + t := by linarith
    have hl : Real.log (1 + t) < (1 / 32 : ℝ) := by
      have := Real.log_nonpos hp.le (by linarith : 1 + t ≤ 1)
      linarith
    simp only [slowFromRest, hn, ite_true, slowVelocity, reparametrizedVelocity,
      logClock, hzero _ hl x, smul_zero]
  · simp only [slowFromRest, hn, ite_false, slowVelocity, reparametrizedVelocity, logClock]

theorem slowFromRest_germ {V : Velocity}
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    {t : ℝ} (ht : -(1 / 2 : ℝ) < t) (x : Space) :
    slowFromRest V =ᶠ[𝓝 (t, x)] slowVelocity V := by
  filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_gt_nhds ht)] with y hy
  exact slowFromRest_eq_near_nonnegative hzero hy y.2

theorem slowForce_residual_near_nonnegative (ν : ℝ) {V : Velocity}
    {t : ℝ} (ht : -1 < t) (x : Space)
    (hV : DifferentiableAt ℝ (fun s => V (s, x)) (logClock t)) :
    slowForce ν V (t, x) = residual ν (slowVelocity V) (t, x) := by
  have hp : 1 + t ≠ 0 := by linarith
  have hτ : HasDerivAt logClock ((1 + t)⁻¹) t := by
    change HasDerivAt (fun s : ℝ => Real.log (1 + s)) ((1 + t)⁻¹) t
    simpa only [one_div, id_eq] using ((hasDerivAt_id t).const_add 1).log hp
  have ha : HasDerivAt (fun s : ℝ => (1 + s)⁻¹) (-((1 + t)⁻¹ ^ 2)) t := by
    convert ((hasDerivAt_id t).const_add 1).inv hp using 1 <;>
      simp [one_div, inv_pow, neg_div]
    rfl
  rw [slowVelocity, residual_reparametrization ν hτ ha x hV]
  simp only [slowForce, quadraticPhase, viscousPhase, logarithmicProfile,
    logClock, pow_one, smul_sub, smul_add, neg_smul]
  module

theorem slowFromRest_force_eq {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (ha : ZeroAdvection V) (ν : ℝ) {t : ℝ} (ht : -(1 / 2 : ℝ) < t) (x : Space) :
    force ν (slowFromRest V) (t, x) = slowForce ν V (t, x) := by
  rw [force_congr_germ (slowFromRest_germ hzero ht x) ν,
    slowForce_residual_near_nonnegative ν (by linarith) x
      ((hV.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) _)]
  have hadv : advection (fun z => slowVelocity V (t, z)) x = 0 := by
    change advection (fun z => (1 + t)⁻¹ • V (logClock t, z)) x = 0
    rw [advection_smul, ha, smul_zero]
  simp only [force, residual, hadv, add_zero]

theorem slowFromRest_force_spatial_time_decay {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V) (ν : ℝ)
    (α : List (Fin 3)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => spatialWord α
        (fun y => force ν (slowFromRest V) (s, y)) x) t‖ ≤
          C * (1 + t)⁻¹ ^ (1 + n) := by
  obtain ⟨C, hC, hbound⟩ := bounded_slowForce_spatial_time_decay ν hV hb ha α n
  refine ⟨C, hC, fun x t ht => ?_⟩
  have he : (fun s => spatialWord α (fun y => force ν (slowFromRest V) (s, y)) x)
      =ᶠ[𝓝 t] fun s => spatialWord α (fun y => slowForce ν V (s, y)) x := by
    filter_upwards [eventually_gt_nhds (show -(1 / 2 : ℝ) < t by linarith)] with s hs
    have hf : (fun y => force ν (slowFromRest V) (s, y)) = fun y => slowForce ν V (s, y) :=
      funext (slowFromRest_force_eq hV hzero ha ν hs)
    rw [hf]
  rw [he.iteratedDeriv_eq n]
  exact hbound x t ht

end ForcedComputation

end

end OAI
