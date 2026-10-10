import OAI.NumberTheory.Jacobsthal.Estimates.EffectiveSurvivors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective

theorem actual_effective_unit_and_coordinate (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    Int.gcd (effectiveIntercept a r qf) (effectiveModulus a r qf : ℤ) = 1 ∧
      ∃! m0 : ℤ,
        (effectiveIntercept a r qf : ℝ)/(p : ℝ) ≤ (m0 : ℝ) ∧
        (m0 : ℝ) < (effectiveIntercept a r qf : ℝ)/(p : ℝ)+(effectiveModulus a r qf : ℝ) ∧
        Int.ModEq (effectiveModulus a r qf : ℤ) ((p : ℤ)*m0) (effectiveIntercept a r qf) := by
  refine ⟨effective_coordinates_gcd a r qf hq,?_⟩
  let m0 := intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)
  have hbounds := intervalM0_bounds p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)
    (effectiveModulus_pos a r qf)
  refine ⟨m0,⟨hbounds.1,hbounds.2,intervalM0_modEq p _ hHp _⟩,?_⟩
  intro m hm
  exact intervalM0_unique p _ hHp _ (effectiveModulus_pos a r qf) m ⟨hm.1,hm.2.1⟩ hm.2.2

end ErdosVarianceEffective

end

end Erdos970

end OAI
