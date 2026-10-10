import OAI.Geometry.CylinderCovering.Convexity.SquaredCapCoverDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SquaredCapData
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCaps
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem

namespace OAI

noncomputable section

namespace AngularCaps

open CylinderCovering

@[simp] theorem squaredData_count (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) :
    (squaredData N a τ η).count = N := rfl

@[simp] theorem squaredData_node (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) :
    (squaredData N a τ η).node = a := rfl

@[simp] theorem squaredData_alpha (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) (j : ℕ) :
    (squaredData N a τ η).alpha j = (1 + a j * a (j + 1)) / 4 := rfl

@[simp] theorem squaredData_beta (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) (j : ℕ) :
    (squaredData N a τ η).beta j = (a j + a (j + 1)) / 4 := rfl

@[simp] theorem squaredData_radius (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) (j : ℕ) :
    (squaredData N a τ η).radius j = squaredRadius τ η := rfl

theorem squaredData_admissible {N : ℕ} {a : ℕ → ℝ} {τ η M : ℝ}
    (hN : 0 < N) (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j < a (j + 1)) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hmesh : ∀ j < N, a (j + 1) - a j ≤ M * τ ^ 2) :
    AngularGeneral.Admissible τ η (max M ((1 / 8 + η) ^ 2))
      (squaredData N a τ η) :=
  withSquaredCaps_admissible hη
    (AngularOrdinaryCaps.ordinaryData_admissible .radial hN ha0 haN ha hη hM hmesh)

theorem squared_cap_cover : SquaredCoverStatement := by
  intro η hη0 hη1 M hM
  have hE : 0 ≤ max M ((1 / 8 + η) ^ 2) := hM.trans (le_max_left _ _)
  obtain ⟨δ, A, hδ, hA, hgeneral⟩ :=
    AngularGeneral.general_cap η hη0 hη1 (max M ((1 / 8 + η) ^ 2)) hE
  refine ⟨δ, A, hδ, hA, ?_⟩
  intro τ hτ hτδ N a hN ha0 haN ha hmesh
  exact hgeneral τ hτ hτδ (squaredData N a τ η)
    (squaredData_admissible hN ha0 haN ha hη0.le hM hmesh)

end AngularCaps

end

end OAI
