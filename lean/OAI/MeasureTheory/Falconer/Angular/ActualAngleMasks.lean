import OAI.MeasureTheory.Falconer.Angular.AngleCoordinateTests
import OAI.MeasureTheory.Falconer.Angular.AngleMaskDerivatives

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def sourceTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) : ℝ → ℝ :=
  smoothAngleMask (sourceUnitDirection ⁻¹' G) (d/100) (by positivity)

theorem sourceTestMask_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (sourceTestMask G d hd) := smoothAngleMask_contDiff _ _ _

theorem sourceTestMask_bounds (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    0 ≤ sourceTestMask G d hd θ ∧ sourceTestMask G d hd θ ≤ 1 := smoothAngleMask_bounds _ _ _ _

theorem sourceTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {θ : ℝ} (hθ : sourceUnitDirection θ ∈ G) : sourceTestMask G d hd θ = 1 :=
  smoothAngleMask_eq_one _ _ _ hθ

theorem sourceTestMask_derivatives (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (sourceTestMask G d hd) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  apply (smoothAngleMask_derivative_bound _ _ _ _ _).trans_eq
  rw [inv_div,div_eq_mul_inv,mul_pow]
  ring

theorem sourceTestMask_support_transfer {G H : Set UnitCircle} {d : ℝ} (hd : 0 < d)
    (htransfer : ∀ (dir : UnitCircle), dir ∈ G → ∀ dir' : UnitCircle, dist (dir:Plane) (dir':Plane) ≤ d → dir' ∈ H) :
    tsupport (sourceTestMask G d hd) ⊆ sourceUnitDirection ⁻¹' H := by
  intro θ hθ
  obtain ⟨φ,hφ,hclose⟩ := mem_thickening_iff.mp (smoothAngleMask_tsupport _ _ _ hθ)
  apply htransfer (sourceUnitDirection φ) hφ (sourceUnitDirection θ)
  change dist (sourceDirection φ) (sourceDirection θ) ≤ d
  have hh := sourceDirection_dist_le φ θ
  rw [dist_comm θ φ] at hclose
  exact hh.trans (by linarith only [hclose, hd])

noncomputable def sourceParallelMask (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (g p : ℕ) (P : CellPath) (T : ℝ) : ℝ → ℝ :=
  sourceTestMask (parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J i p) T)
    (sourceAngularRadius N sig (p-g)) (sourceAngularRadius_pos _ _ _)

noncomputable def sourceProjectionMask (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (p u : ℕ) (P : CellPath) (T : ℝ) : ℝ → ℝ :=
  sourceTestMask (projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J i u) T)
    (sourceAngularRadius N sig (u-p)) (sourceAngularRadius_pos _ _ _)

theorem sourceParallelMask_antipodal (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (g p : ℕ) (P : CellPath) (T : ℝ) :
    Function.Periodic (sourceParallelMask N sig J i Q ρ g p P T) Real.pi :=
  smoothAngleMask_periodic (parallelAngleGood_periodic Q ρ g p P _ T) _ _

theorem sourceProjectionMask_antipodal (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (p u : ℕ) (P : CellPath) (T : ℝ) :
    Function.Periodic (sourceProjectionMask N sig J i Q ρ p u P T) Real.pi :=
  smoothAngleMask_periodic (projectionAngleGood_periodic Q ρ p u P _ T) _ _

theorem uniform_parallel_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (T : ℝ),
      tsupport (sourceParallelMask N sig J i Q ρ g p P T) ⊆
        sourceUnitDirection ⁻¹' parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J (i+1) p) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_parallel_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q ρ g p hgp P i dir dir' (by simpa using hdist))).trans hdir

theorem uniform_projection_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (T : ℝ),
      tsupport (sourceProjectionMask N sig J i Q ρ p u P T) ⊆
        sourceUnitDirection ⁻¹' projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J (i+1) u) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_projection_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q hQ ρ p u hpu P hP i dir dir' (by simpa using hdist))).trans hdir

end PlanarFalconer

end OAI
