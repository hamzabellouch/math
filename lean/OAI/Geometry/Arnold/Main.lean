import OAI.Geometry.Arnold.Degeneracy

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample

/-- The Hamiltonian counterexample, with the complete fixed set, the lower bound
for all smooth functions, and a genuine nonzero quotient-tangent eigenvector. -/
theorem main :
    ∃ φ : Q3 ≃ Q3, IsHamiltonian φ ∧ (fixedSet φ).encard = 3 ∧
      (3 : ℕ∞) < 4 ∧ 4 ≤ criticalNumber ∧ HasDegenerateFixedPoint φ := by
  exact ⟨Construction.mainEquiv, Construction.main_isHamiltonian,
    Construction.main_fixed_encard, by norm_num, four_le_criticalNumber,
    Construction.main_degenerate⟩

end ArnoldCounterexample

end

end OAI
