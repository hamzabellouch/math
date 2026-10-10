import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RiemannianExponentialInputs

namespace OAI

/-! # Recovering the topological chart input from the regularity input

Exponential existence is proved by the integral-curve construction. The
remaining chart assertion follows from the already required exponential
diffeomorphism after changing from finite basis coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem DixmierExponentialDiffeomorphismInput.toTopological
    (h : DixmierExponentialDiffeomorphismInput (E := E) (G := G)) :
    DixmierExponentialInput (E := E) (G := G) := by
  rintro ⟨a, ⟨T⟩⟩
  refine ⟨exists_groupExponential, ?_⟩
  intro Exp hExp
  obtain ⟨φ, hφ, _, _⟩ := h a T Exp hExp
  let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  let e := b.equivFun.toContinuousLinearEquiv.toHomeomorph
  refine ⟨e.trans φ, fun v => ?_⟩
  change φ (b.equivFun v) = Exp v
  rw [hφ, b.equivFun.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
