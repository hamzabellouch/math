import OAI.Geometry.CylinderCovering.Cartesian.CoverDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.General
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCaps

namespace OAI

open Set
namespace CylinderCovering.CartesianCaps

theorem cartesianData_admissible {N : ℕ} {a : ℕ → ℝ} {τ η M : ℝ}
    (hN : 0 < N) (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j < a (j+1))
    (hτ : τ ∈ Icc (0 : ℝ) (1/4)) (hη : η ∈ Ioc (0 : ℝ) 1) (hM : 0 ≤ M)
    (hmesh : ∀ j < N, a (j+1)-a j ≤ M*τ^2) :
    AngularGeneral.Admissible τ η (max M 12) (cartesianData N a τ η) := by
  apply cartesian_admissible τ η M _ hτ hη
  exact AngularOrdinaryCaps.ordinaryData_admissible .radial hN ha0 haN ha hη.1.le hM hmesh

theorem cartesianData_parameters (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) :
    (cartesianData N a τ η).count = N ∧
    (cartesianData N a τ η).node = a ∧
    (∀ j, (cartesianData N a τ η).alpha j = (1+a j*a (j+1))/4) ∧
    (∀ j, (cartesianData N a τ η).beta j = (a j+a (j+1))/4) ∧
    ∀ j q, (cartesianData N a τ η).radius j q = cap τ η q := by
  exact ⟨rfl,rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl⟩

end CylinderCovering.CartesianCaps

end OAI
