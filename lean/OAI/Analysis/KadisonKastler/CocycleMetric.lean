import OAI.Analysis.KadisonKastler.QuadraticIteration
import OAI.Analysis.KadisonKastler.BoundaryImprovement
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Algebra.Star.Unitary

namespace OAI

/-! # The complete metric space of uniformly bounded unitary families

The cocycle defect is continuous for the uniform norm. This supplies the
metric-space part of the boundary correction iteration.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance : CStarAlgebra (G →ᵇ B) where

local instance : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe

/-- Evaluation of an actual uniformly bounded unitary family. -/
def unitaryFamilyEval (V : unitary (G →ᵇ B)) (g : G) : unitary B :=
  ⟨V.val g, by
    have h₁ := congrArg (fun f : G →ᵇ B => f g)
      (Unitary.star_mul_self_of_mem V.property)
    have h₂ := congrArg (fun f : G →ᵇ B => f g)
      (Unitary.mul_star_self_of_mem V.property)
    exact ⟨h₁, h₂⟩⟩

/-- The cocycle error as a bounded function of the two group variables. -/
def unitaryCocycleError (α : G →* (B ≃⋆ₐ[ℂ] B)) (V : unitary (G →ᵇ B)) :
    (G × G) →ᵇ B :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => V.val p.1 * α p.1 (V.val p.2) - V.val (p.1 * p.2)) 2 (by
      rintro ⟨g, h⟩
      have h₁ : ‖V.val g‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval V g)
      have h₂ : ‖α g (V.val h)‖ ≤ 1 :=
        norm_unitary_le_one (Unitary.map (StarMonoidHom.ofClass (α g)) (unitaryFamilyEval V h))
      have h₃ : ‖V.val (g * h)‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval V (g * h))
      have hp : ‖V.val g‖ * ‖α g (V.val h)‖ ≤ 1 := by
        simpa only [one_mul] using mul_le_mul h₁ h₂
          (norm_nonneg (α g (V.val h))) (by norm_num : (0 : ℝ) ≤ 1)
      exact (norm_sub_le _ _).trans
        ((add_le_add ((norm_mul_le _ _).trans hp) h₃).trans_eq
          (by norm_num)))

/-- The supremum of all cocycle errors. -/
def unitaryCocycleDefect (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : ℝ := ‖unitaryCocycleError α V‖

theorem unitaryCocycleDefect_nonneg (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : 0 ≤ unitaryCocycleDefect α V := norm_nonneg _

theorem unitaryCocycleDefect_eq_zero_iff (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : unitaryCocycleDefect α V = 0 ↔
      ∀ g h, V.val g * α g (V.val h) = V.val (g * h) := by
  rw [unitaryCocycleDefect, norm_eq_zero]
  constructor
  · intro h g k
    exact sub_eq_zero.mp (congrArg (fun f : (G × G) →ᵇ B => f (g, k)) h)
  · intro h
    ext ⟨g, k⟩
    exact sub_eq_zero.mpr (h g k)

private theorem unitary_cocycle_error_difference_le
    (α : G →* (B ≃⋆ₐ[ℂ] B)) (V W : unitary (G →ᵇ B)) (g h : G) :
    ‖unitaryCocycleError α V (g, h) - unitaryCocycleError α W (g, h)‖ ≤
      3 * ‖V.val - W.val‖ := by
  let c := ‖V.val - W.val‖
  have he (g : G) : ‖V.val g - W.val g‖ ≤ c :=
    (V.val - W.val).norm_coe_le_norm g
  have hv : ‖α g (V.val h)‖ ≤ 1 :=
    norm_unitary_le_one (Unitary.map (StarMonoidHom.ofClass (α g)) (unitaryFamilyEval V h))
  have hw : ‖W.val g‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval W g)
  have hα : ‖α g (V.val h - W.val h)‖ ≤ c := by
    have hi : ‖α g (V.val h - W.val h)‖ = ‖V.val h - W.val h‖ :=
      NonUnitalStarAlgHom.norm_map (α g).toStarAlgHom (α g).injective _
    rw [hi]
    exact he h
  change ‖(V.val g * α g (V.val h) - V.val (g * h)) -
    (W.val g * α g (W.val h) - W.val (g * h))‖ ≤ 3 * c
  have hid : (V.val g * α g (V.val h) - V.val (g * h)) -
      (W.val g * α g (W.val h) - W.val (g * h)) =
      (V.val g - W.val g) * α g (V.val h) +
        W.val g * α g (V.val h - W.val h) - (V.val (g * h) - W.val (g * h)) := by
    rw [map_sub]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(V.val g - W.val g) * α g (V.val h)‖ +
        ‖W.val g * α g (V.val h - W.val h)‖ + ‖V.val (g * h) - W.val (g * h)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c * 1 + 1 * c + c := by
      exact add_le_add (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul (he g) hv (norm_nonneg _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul hw hα (norm_nonneg _) (by norm_num)))) (he _)
    _ = _ := by ring

theorem unitaryCocycleError_lipschitz (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    LipschitzWith 3 (unitaryCocycleError α) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖unitaryCocycleError α V - unitaryCocycleError α W‖ ≤
    (3 : ℝ) * ‖V.val - W.val‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  rintro ⟨g, h⟩
  exact unitary_cocycle_error_difference_le α V W g h

theorem continuous_unitaryCocycleDefect (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    Continuous (unitaryCocycleDefect α) :=
  (unitaryCocycleError_lipschitz α).continuous.norm

end

end KadisonKastler

end OAI
