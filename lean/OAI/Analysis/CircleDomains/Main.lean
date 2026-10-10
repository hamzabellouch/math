import OAI.Analysis.CircleDomains.Theorems

namespace OAI

/-! Circle-domain uniformization and rigidity under conformal removability. -/
open Set CircleDomainRigidity
noncomputable section
namespace Problem047

theorem koebe_circle_domain :
    ∀ U : Set Sphere, IsOpen U → IsConnected U →
      ∃ (V : Set Sphere) (f : Sphere → Sphere),
        IsCircleDomain V ∧ IsConformalEquivalence f U V :=
  CircleDomainRigidity.koebeCircleDomainConjecture

theorem removability_implies_rigidity :
    ∀ (U V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain U → IsCircleDomain V →
      IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
      ∃ M : Mobius, ∀ p ∈ U, f p = M • p :=
  CircleDomainRigidity.circleDomainRemovabilityRigidity

end Problem047

end

end OAI
