import OAI.Geometry.EinsteinFour.JacobiSchemeError
import OAI.Geometry.EinsteinFour.JacobiMeshError
import OAI.Geometry.EinsteinFour.JacobiPreconjugate

namespace OAI

/-! Preconjugate positivity from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

def meshStep (t : ℝ) (N : ℕ) : ℝ := t / (N + 1)

def meshCurvature (R : ℝ → NormalMatrix) (t : ℝ) (N i : ℕ) : NormalMatrix :=
  R ((i : ℝ) * meshStep t N)

theorem meshStep_tendsto (t : ℝ) : Tendsto (meshStep t) atTop (nhds 0) := by
  change Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (nhds 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)

/-- Precisely the local ODE and regularity bounds used by the discretization.
All constants can be chosen on a compact interval of a smooth Jacobi curve. -/
structure RegularJacobi (t : ℝ) where
  R : ℝ → NormalMatrix
  J : ℝ → NormalMatrix
  V : ℝ → NormalMatrix
  K : ℝ
  Lx : ℝ
  Lv : ℝ
  F : ℝ
  K_nonneg : 0 ≤ K
  Lx_nonneg : 0 ≤ Lx
  Lv_nonneg : 0 ≤ Lv
  F_nonneg : 0 ≤ F
  initial_position : J 0 = 0
  initial_velocity : V 0 = 1
  symmetric : ∀ s, (R s)ᵀ = R s
  curvature_bound : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ K
  position_derivative : ∀ s ∈ Set.Icc 0 t, HasDerivAt J (V s) s
  velocity_derivative : ∀ s ∈ Set.Icc 0 t, HasDerivAt V (-(R s * J s)) s
  velocity_lipschitz : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
    ‖V s - V r‖ ≤ Lx * |s - r|
  acceleration_lipschitz : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
    ‖-(R s * J s) - -(R r * J r)‖ ≤ Lv * |s - r|
  force_bound : ∀ s ∈ Set.Icc 0 t, ‖R s * J s‖ ≤ F

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

def localError : ℝ := d.Lx + d.Lv + d.F

def growth : ℝ := 1 + 2 * d.K

def positionError (N : ℕ) : ℝ := d.localError * meshStep t N * Real.exp (d.growth * t)

def velocityError (N : ℕ) : ℝ :=
  (d.localError * t * Real.exp (d.growth * t) + d.Lx) * meshStep t N

theorem positionError_tendsto : Tendsto d.positionError atTop (nhds 0) := by
  change Tendsto (fun N : ℕ => d.localError * meshStep t N * Real.exp (d.growth * t))
    atTop (nhds 0)
  simpa only [positionError, mul_zero, zero_mul] using
    ((meshStep_tendsto t).const_mul d.localError).mul_const (Real.exp (d.growth * t))

theorem velocityError_tendsto : Tendsto d.velocityError atTop (nhds 0) := by
  change Tendsto (fun N : ℕ =>
    (d.localError * t * Real.exp (d.growth * t) + d.Lx) * meshStep t N) atTop (nhds 0)
  simpa only [velocityError, mul_zero] using
    (meshStep_tendsto t).const_mul (d.localError * t * Real.exp (d.growth * t) + d.Lx)

theorem uniform_errors (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i : ℕ, i ≤ N + 1 →
        ‖relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) i -
          normalizedJacobi d.J ((i : ℝ) * meshStep t N)‖ ≤ d.positionError N) ∧
      (∀ i : ℕ, i ≤ N →
        ‖discreteVelocity (meshCurvature d.R t N) (meshStep t N) (i + 1) -
          d.V ((i : ℝ) * meshStep t N)‖ ≤ d.velocityError N) := by
  have hc : 0 ≤ d.localError := add_nonneg (add_nonneg d.Lx_nonneg d.Lv_nonneg) d.F_nonneg
  have hk : 0 ≤ d.growth := by dsimp [growth]; linarith [d.K_nonneg]
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  filter_upwards [(meshStep_tendsto t).eventually (gt_mem_nhds zero_lt_one)] with N hN
  have hh : 0 < meshStep t N := div_pos ht (by positivity)
  have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
    simp only [meshStep, Nat.cast_add, Nat.cast_one]
    field_simp
  have herr (i : ℕ) (hi : i ≤ N + 1) :
      ‖discretePosition (meshCurvature d.R t N) (meshStep t N) i -
        d.J (i * meshStep t N)‖ +
      ‖discreteVelocity (meshCurvature d.R t N) (meshStep t N) i -
        d.V (i * meshStep t N)‖ ≤
        d.localError * i * meshStep t N ^ 2 * Real.exp (d.growth * i * meshStep t N) := by
    have hit : (i : ℝ) * meshStep t N ≤ t := by
      calc
        _ ≤ ((N + 1 : ℕ) : ℝ) * meshStep t N :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le
        _ = t := htmesh
    exact discreteJacobi_error hh.le hN.le hit d.K_nonneg d.Lx_nonneg d.Lv_nonneg
      d.F_nonneg d.initial_position d.initial_velocity d.curvature_bound
      d.position_derivative d.velocity_derivative d.velocity_lipschitz
      d.acceleration_lipschitz d.force_bound
  constructor
  · apply relative_discrete_error hh hc hk htmesh.le d.initial_position hd0
    intro i hi
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (herr i hi)
  · apply next_discrete_velocity_error hh hc hk d.Lx_nonneg htmesh.le
    · intro i hi
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans (herr i hi)
    · exact d.velocity_lipschitz

/-- The Jacobi ODE implies positivity of the finite curvature matrices. -/
theorem curvatureDirichlet_eventually_posDef (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    ∀ᶠ N : ℕ in atTop,
      (curvatureDirichlet t (fun i : Fin N =>
        d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1)).PosDef := by
  have hcJ : ContinuousOn d.J (Set.Icc 0 t) := fun s hs =>
    (d.position_derivative s hs).continuousAt.continuousWithinAt
  have hcV : ContinuousOn d.V (Set.Icc 0 t) := fun s hs =>
    (d.velocity_derivative s hs).continuousAt.continuousWithinAt
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  have he := d.uniform_errors ht
  exact curvatureDirichlet_eventually_posDef_of_approximation ht (meshCurvature d.R t)
    (fun N i => d.symmetric _) (normalizedJacobi_continuousOn hcJ hd0) hcV
    (normalizedJacobi_zero hd0) d.initial_velocity
    (normalizedJacobi_isUnit d.initial_position hd0 hpre)
    d.positionError_tendsto d.velocityError_tendsto
    (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
