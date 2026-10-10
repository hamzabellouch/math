import Mathlib
import OAI.Algebra.GroupRing.ConcreteModel

namespace OAI

section

namespace TorsionFreeZeroDivisors
noncomputable section
/-- A torsion-free group with a finite 2-dimensional K(G,1) and zero divisors.
Both zero-divisor factors are nonzero, and torsion-freeness is ordinary
absence of all nontrivial finite-order elements. -/
theorem main : MainTheorem := by
  obtain ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,hz⟩ := SampleGraph.exists_nonzero_factors
  exact ⟨ConcreteGroup.G rep r,inferInstance,inferInstance,
    ConcreteTorsion.torsion_free rep r x y hL hd hr ha,
    ConcreteModel.has_model rep r x y hL hd hr ha,
    ConcreteFactors.alpha rep r x,ConcreteFactors.beta rep r y,hx,hy,hz⟩
end
end TorsionFreeZeroDivisors

end

end OAI
