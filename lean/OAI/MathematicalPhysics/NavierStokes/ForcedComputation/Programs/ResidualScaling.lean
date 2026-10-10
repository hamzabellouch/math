import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-!
# Residual force under startup and changes of clock

The fields and differential operators are the concrete flat-coordinate ones
already used by the shear realization. In particular, `residual` includes the
convective term, which need not vanish for a spatial suspension.
-/

noncomputable section

open scoped BigOperators ContDiff Topology
open ShearFlows

namespace ForcedComputation

def residual (ν : ℝ) (V : Velocity) : Velocity :=
  fun y => timeDerivative V y.1 y.2 + advection (fun x => V (y.1, x)) y.2 -
    ν • laplacian (fun x => V (y.1, x)) y.2

theorem derivative_smul (a : ℝ) (W : Space → Space) (j : Fin 3) (x : Space) :
    derivative (fun y => a • W y) j x = a • derivative W j x := by
  unfold derivative
  rw [show (fun y => a • W y) = a • W from rfl, fderiv_const_smul_field]
  rfl

theorem laplacian_smul (a : ℝ) (W : Space → Space) (x : Space) :
    laplacian (fun y => a • W y) x = a • laplacian W x := by
  unfold laplacian
  have hd (j : Fin 3) : derivative (fun y => a • W y) j =
      fun y => a • derivative W j y := funext (derivative_smul a W j)
  simp_rw [hd]
  change (∑ j, fderiv ℝ (a • derivative W j) x (basis j)) = _
  simp only [fderiv_const_smul_field, Pi.smul_apply, smul_apply, Finset.smul_sum]

theorem advection_smul (a : ℝ) (W : Space → Space) (x : Space) :
    advection (fun y => a • W y) x = a ^ 2 • advection W x := by
  unfold advection
  rw [show (fun y => a • W y) = a • W from rfl, fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, map_smul, smul_smul, pow_two]

theorem divergence_smul (a : ℝ) (W : Space → Space) (x : Space) :
    divergence (fun y => a • W y) x = a * divergence W x := by
  simp only [divergence, derivative_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

def rampVelocity (α : ℝ → ℝ) (W : Space → Space) : Velocity :=
  fun y => α y.1 • W y.2

/-- Formula (steady-force) in the eventually stationary forcing manuscript. -/
theorem residual_ramp (ν : ℝ) (α : ℝ → ℝ) (W : Space → Space)
    {t : ℝ} (hα : DifferentiableAt ℝ α t) (x : Space) :
    residual ν (rampVelocity α W) (t, x) =
      deriv α t • W x + α t ^ 2 • advection W x - ν • (α t • laplacian W x) := by
  have ht : timeDerivative (rampVelocity α W) t x = deriv α t • W x :=
    (hα.hasDerivAt.smul_const (W x)).deriv
  change timeDerivative (rampVelocity α W) t x +
      advection (fun y => α t • W y) x - ν • laplacian (fun y => α t • W y) x = _
  rw [ht, advection_smul, laplacian_smul]

theorem ramp_initial_zero {α : ℝ → ℝ} (hα : α 0 = 0) (W : Space → Space) (x : Space) :
    rampVelocity α W (0, x) = 0 := by
  simp [rampVelocity, hα]

theorem ramp_solenoidal (α : ℝ → ℝ) {W : Space → Space}
    (hW : ∀ x, divergence W x = 0) : Solenoidal (rampVelocity α W) := by
  intro t x
  change divergence (fun y => α t • W y) x = 0
  rw [divergence_smul, hW x, mul_zero]

/-- Once a startup ramp is locally one, its force is the stationary residual. -/
theorem residual_ramp_of_eventually_one (ν : ℝ) {α : ℝ → ℝ} (W : Space → Space)
    {t : ℝ} (hα : α =ᶠ[𝓝 t] fun _ => 1) (x : Space) :
    residual ν (rampVelocity α W) (t, x) = advection W x - ν • laplacian W x := by
  have ha : α t = 1 := hα.self_of_nhds
  have hd : HasDerivAt α 0 t := (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hα
  rw [residual_ramp ν α W hd.differentiableAt x, hd.deriv, ha]
  simp

/-- The endpoint of the stationary interval is included; differentiability
forces the startup derivative to agree with the constant right-hand tail. -/
theorem residual_ramp_on_tail (ν : ℝ) {α : ℝ → ℝ} (W : Space → Space)
    (htail : ∀ s, 1 ≤ s → α s = 1) {t : ℝ} (ht : 1 ≤ t)
    (hα : DifferentiableAt ℝ α t) (x : Space) :
    residual ν (rampVelocity α W) (t, x) = advection W x - ν • laplacian W x := by
  have hu : UniqueDiffWithinAt ℝ (Set.Ici 1) t := uniqueDiffOn_Ici 1 t ht
  have hw : HasDerivWithinAt α 0 (Set.Ici 1) t :=
    (hasDerivWithinAt_const t (Set.Ici 1) (1 : ℝ)).congr_of_mem htail ht
  have hd : deriv α t = 0 := by
    rw [← hα.derivWithin hu]
    exact hw.derivWithin hu
  rw [residual_ramp ν α W hα x, hd, htail t ht]
  simp

def reparametrizedVelocity (τ a : ℝ → ℝ) (V : Velocity) : Velocity :=
  fun y => a y.1 • V (τ y.1, y.2)

/-- The full clock-force formula, including convection and the clock acceleration. -/
theorem residual_reparametrization (ν : ℝ) {τ a : ℝ → ℝ} {V : Velocity}
    {t da : ℝ} (hτ : HasDerivAt τ (a t) t) (ha : HasDerivAt a da t)
    (x : Space) (hV : DifferentiableAt ℝ (fun s => V (s, x)) (τ t)) :
    residual ν (reparametrizedVelocity τ a V) (t, x) =
      da • V (τ t, x) - ν • (a t • laplacian (fun y => V (τ t, y)) x) +
        a t ^ 2 • (timeDerivative V (τ t) x + advection (fun y => V (τ t, y)) x) := by
  have hd : timeDerivative (reparametrizedVelocity τ a V) t x =
      a t • (a t • timeDerivative V (τ t) x) + da • V (τ t, x) := by
    exact (ha.smul (hV.hasDerivAt.scomp t hτ)).deriv
  change timeDerivative (reparametrizedVelocity τ a V) t x +
      advection (fun y => a t • V (τ t, y)) x -
        ν • laplacian (fun y => a t • V (τ t, y)) x = _
  rw [hd, advection_smul, laplacian_smul]
  simp only [pow_two, smul_add, smul_smul]
  abel

theorem reparametrized_initial_zero {τ a : ℝ → ℝ} {V : Velocity}
    (hτ : τ 0 = 0) (hV : ∀ x, V (0, x) = 0) (x : Space) :
    reparametrizedVelocity τ a V (0, x) = 0 := by
  simp [reparametrizedVelocity, hτ, hV]

theorem reparametrized_solenoidal (τ a : ℝ → ℝ) {V : Velocity}
    (hV : Solenoidal V) : Solenoidal (reparametrizedVelocity τ a V) := by
  intro t x
  change divergence (fun y => a t • V (τ t, y)) x = 0
  rw [divergence_smul, hV, mul_zero]

end ForcedComputation

end

end OAI
