import OAI.MathematicalPhysics.Transonic.Profile.Equations

namespace OAI

section
noncomputable section
open scoped ContDiff
namespace SepticProfile

def RelativisticProfileExists : Prop :=
  ∃ (beta : ℝ) (g : ℝ → ℝ),
    1 < beta ∧ beta*(ell + Real.sqrt ell) < 3 ∧
    ContDiffOn ℝ ∞ g (Set.Ici 0) ∧
    let v : ℝ → ℝ := fun y => y*g (y^2)
    (∀ y : ℝ, 0 ≤ y → |v y| < 1) ∧
    (∀ y : ℝ, 0 ≤ y →
      profileDenom ell y (v y) * deriv v y = profileNumer ell beta y (v y)) ∧
    (∀ y : ℝ, 0 < y → v y < y ∧ y*v y < 1) ∧
    0 < sonicRadius beta ∧ sonicRadius beta < 1 ∧
    (∀ y : ℝ, 0 ≤ y →
      (velocityToU y (v y) = sonicSpeed ↔ y = sonicRadius beta)) ∧
    0 < deriv (fun y => velocityToU y (v y)) (sonicRadius beta)

end SepticProfile

end
end

end OAI
