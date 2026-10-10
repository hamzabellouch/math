import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualScaling
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Reparametrization

namespace OAI

/-!
# The force produced by a logarithmic clock

This is the residual calculation in the slow-clock construction, with the
linear viscous term separated from the quadratic material acceleration.
-/

noncomputable section
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

def slowVelocity (V : Velocity) : Velocity :=
  reparametrizedVelocity logClock (fun t => (1 + t)⁻¹) V

def quadraticPhase (V : Velocity) (x : Space) (s : ℝ) : Space :=
  timeDerivative V s x + advection (fun y => V (s, y)) x - V (s, x)

def viscousPhase (V : Velocity) (x : Space) (s : ℝ) : Space :=
  laplacian (fun y => V (s, y)) x

def slowForce (ν : ℝ) (V : Velocity) : Velocity := fun y =>
  logarithmicProfile 2 (quadraticPhase V y.2) y.1 -
    ν • logarithmicProfile 1 (viscousPhase V y.2) y.1

theorem slowForce_eq_residual (ν : ℝ) {V : Velocity} {t : ℝ} (ht : 0 ≤ t)
    (x : Space) (hV : DifferentiableAt ℝ (fun s => V (s, x)) (logClock t)) :
    slowForce ν V (t, x) = residual ν (slowVelocity V) (t, x) := by
  have hp : 1 + t ≠ 0 := by linarith
  have hτ : HasDerivAt logClock ((1 + t)⁻¹) t := by
    simpa only [one_div] using logClock_hasDerivAt ht
  have ha : HasDerivAt (fun s : ℝ => (1 + s)⁻¹) (-((1 + t)⁻¹ ^ 2)) t := by
    convert ((hasDerivAt_id t).const_add 1).inv hp using 1 <;>
      simp [one_div, inv_pow, neg_div]
    rfl
  rw [slowVelocity, residual_reparametrization ν hτ ha x hV]
  simp only [slowForce, quadraticPhase, viscousPhase, logarithmicProfile,
    logClock, pow_one, smul_sub, smul_add, neg_smul]
  module

/-- Uniform phase derivative bounds give exactly the slow-clock force estimate.
The hypotheses refer to the original bounded periodic profiles, not to the
force or to its desired decay. -/
theorem slowForce_time_decay (ν : ℝ) {V : Velocity}
    (hQ : ∀ x, ContDiff ℝ ∞ (quadraticPhase V x))
    (hD : ∀ x, ContDiff ℝ ∞ (viscousPhase V x))
    (hQB : UniformTimeBounds (quadraticPhase V))
    (hDB : UniformTimeBounds (viscousPhase V)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => slowForce ν V (s, x)) t‖ ≤
        C * (1 + t)⁻¹ ^ (1 + n) := by
  obtain ⟨A, hA, hQA⟩ := logarithmicProfile_uniform_decay 2 n hQ hQB
  obtain ⟨B, hB, hDB⟩ := logarithmicProfile_uniform_decay 1 n hD hDB
  refine ⟨A + ‖ν‖ * B, by positivity, fun x t ht => ?_⟩
  have hqt := logarithmicProfile_contDiffAt 2 (hQ x) (show -1 < t by linarith)
  have hdt := logarithmicProfile_contDiffAt 1 (hD x) (show -1 < t by linarith)
  change ‖iteratedDeriv n (fun s => logarithmicProfile 2 (quadraticPhase V x) s -
    ν • logarithmicProfile 1 (viscousPhase V x) s) t‖ ≤ _
  rw [iteratedDeriv_fun_sub (hqt.of_le (by simp))
      ((hdt.const_smul ν).of_le (by simp)), iteratedDeriv_fun_const_smul_field]
  have hinv : 0 ≤ (1 + t)⁻¹ := by positivity
  have hinvle : (1 + t)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)
  have hpow : (1 + t)⁻¹ ^ (2 + n) ≤ (1 + t)⁻¹ ^ (1 + n) := by
    calc
      _ = (1 + t)⁻¹ ^ (1 + n) * (1 + t)⁻¹ := by rw [← pow_succ]; congr 1; omega
      _ ≤ (1 + t)⁻¹ ^ (1 + n) * 1 :=
        mul_le_mul_of_nonneg_left hinvle (pow_nonneg hinv _)
      _ = _ := mul_one _
  calc
    _ ≤ ‖iteratedDeriv n (logarithmicProfile 2 (quadraticPhase V x)) t‖ +
        ‖ν • iteratedDeriv n (logarithmicProfile 1 (viscousPhase V x)) t‖ := norm_sub_le _ _
    _ ≤ A * (1 + t)⁻¹ ^ (2 + n) + ‖ν‖ * (B * (1 + t)⁻¹ ^ (1 + n)) := by
      rw [norm_smul]
      exact add_le_add (hQA x t ht) (mul_le_mul_of_nonneg_left (hDB x t ht) (norm_nonneg ν))
    _ ≤ A * (1 + t)⁻¹ ^ (1 + n) + ‖ν‖ * (B * (1 + t)⁻¹ ^ (1 + n)) :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hA) le_rfl
    _ = _ := by ring

end ForcedComputation

end

end OAI
