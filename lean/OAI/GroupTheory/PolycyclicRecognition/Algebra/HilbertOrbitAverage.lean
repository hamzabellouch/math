import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.Module.Equiv.Basic

namespace OAI

/-! # Hilbert averaging over a group orbit

The closed convex hull of a unitary orbit has a fixed vector of minimal norm.
This requires no invariant mean on the acting group. It supplies the averaging
step in the construction of ergodic conditional component measures.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)

/-- The closed convex hull of the actual orbit. -/
def hilbertOrbitHull : Set E := closure (convexHull ℝ (range (fun g => ρ g x)))

theorem hilbertOrbitHull_nonempty : (hilbertOrbitHull ρ x).Nonempty :=
  (Set.range_nonempty (fun g => ρ g x)).convexHull.closure

theorem hilbertOrbitHull_convex : Convex ℝ (hilbertOrbitHull ρ x) :=
  (convex_convexHull ℝ _).closure

/-- Every acting isometry preserves the closed convex hull. -/
theorem hilbertOrbitHull_map (g : G) {y : E} (hy : y ∈ hilbertOrbitHull ρ x) :
    ρ g y ∈ hilbertOrbitHull ρ x := by
  apply closure_minimal (t := (ρ g) ⁻¹' hilbertOrbitHull ρ x) ?_
    (isClosed_closure.preimage (ρ g).continuous) hy
  apply convexHull_min
  · rintro _ ⟨h, rfl⟩
    apply subset_closure
    apply subset_convexHull ℝ
    refine ⟨g * h, ?_⟩
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl
  · exact (hilbertOrbitHull_convex ρ x).linear_preimage (ρ g).toLinearEquiv.toLinearMap

variable [CompleteSpace E]

/-- A fixed vector is a norm limit of finite convex combinations of the orbit. -/
theorem exists_fixed_in_hilbertOrbitHull :
    ∃ y ∈ hilbertOrbitHull ρ x, ∀ g : G, ρ g y = y := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hilbertOrbitHull_nonempty ρ x) isClosed_closure.isComplete
    (hilbertOrbitHull_convex ρ x) (0 : E)
  refine ⟨y, hy, fun g => ?_⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero
    (hilbertOrbitHull_convex ρ x) hy).mp hmin (ρ g y) (hilbertOrbitHull_map ρ x g hy)
  have hn : ‖ρ g y‖ = ‖y‖ := (ρ g).norm_map y
  have hu := real_inner_le_norm y (ρ g y)
  have hl : ‖y‖ ^ 2 ≤ inner ℝ y (ρ g y) := by
    have hi' : -(inner ℝ y (ρ g y)) ≤ -‖y‖ ^ 2 := by
      simpa only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
        neg_sub, sub_nonpos] using hi
    linarith
  have he : inner ℝ (ρ g y) y = ‖y‖ ^ 2 := by
    rw [real_inner_comm]
    rw [hn] at hu
    nlinarith
  exact eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) hn.le he

section IsometricAction

variable [DistribMulAction G E] [SMulCommClass G ℝ E] [IsIsometricSMul G E]

/-- The bundled unitary representation of a real linear isometric action. -/
def isometricLinearAction : G →* (E ≃ₗᵢ[ℝ] E) where
  toFun g :=
    { DistribMulAction.toLinearEquiv ℝ E g with
      norm_map' := fun v => by
        change ‖g • v‖ = ‖v‖
        have h := (isometry_smul E g).dist_eq v 0
        simpa only [smul_zero, dist_zero_right] using h }
  map_one' := by ext v; exact one_smul G v
  map_mul' g h := by ext v; exact mul_smul g h v

/-- The convex orbit averaging theorem in the unbundled action notation. -/
theorem exists_fixed_in_convex_orbit (x : E) :
    ∃ y ∈ closure (convexHull ℝ (range (fun g : G => g • x))),
      ∀ g : G, g • y = y :=
  exists_fixed_in_hilbertOrbitHull (isometricLinearAction (G := G) (E := E)) x

end IsometricAction

end PolycyclicRecognition

end

end OAI
