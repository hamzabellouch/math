import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightFactorModel

namespace OAI

/-! # Common exponential coordinates on the intersection of the factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)}
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/-- The recorded intersection theorem supplies a single tangent vector for
both factor coordinates, using only injectivity of their actual inclusions. -/
theorem factor_overlap_coordinates (n : F.N.carrier) (d : F.D.carrier)
    (he : F.inclusionN n = F.inclusionD d) :
    ∃ x : GroupLieAlgebra (𝓘(ℝ,E)) G, ∃ hx : x ∈ T.kernelIdeal, ∃ hy : x ∈ H,
      n = F.ExpN (F.N.equiv ⟨x,hx⟩) ∧ d = F.ExpD (F.D.equiv ⟨x,hy⟩) := by
  have hm : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n,rfl⟩,⟨d,he.symm⟩⟩
  rw [F.overlap] at hm
  obtain ⟨x,hx,hg⟩ := hm
  exact ⟨x,hx.1,hx.2,
    F.closedN.injective (hg.symm.trans (F.compatibleN ⟨x,hx.1⟩).symm),
    F.closedD.injective ((he.symm.trans hg.symm).trans (F.compatibleD ⟨x,hx.2⟩).symm)⟩

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
