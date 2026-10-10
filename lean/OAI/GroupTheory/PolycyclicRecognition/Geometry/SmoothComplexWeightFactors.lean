import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.DiscreteNilpotentLieGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicExponentialSmooth

namespace OAI

/-! # Smooth exponential coordinates on the actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

omit [H.IsCartanSubalgebra] in
theorem contMDiff_expN :
    ContMDiff (𝓘(ℝ,F.N.modelSpace)) (𝓘(ℝ,F.N.modelSpace)) ∞
      (fun x : F.N.modelSpace => F.ExpN x) := by
  let : MetricSpace F.N.carrier := F.closedN.isEmbedding.comapMetricSpace F.inclusionN
  let := F.N.tangent_nilpotent T.kernelIdeal_nilpotent
  obtain ⟨m,⟨A⟩⟩ := nonempty_triangularAdjoint_of_nilpotent
    (GroupLieAlgebra (𝓘(ℝ,F.N.modelSpace)) F.N.carrier)
  exact intrinsic_exponential_contMDiff A F.ExpN F.isExpN

theorem contMDiff_expD :
    ContMDiff (𝓘(ℝ,F.D.modelSpace)) (𝓘(ℝ,F.D.modelSpace)) ∞
      (fun x : F.D.modelSpace => F.ExpD x) := by
  let : MetricSpace F.D.carrier := F.closedD.isEmbedding.comapMetricSpace F.inclusionD
  let := F.D.tangent_nilpotent (inferInstance : LieRing.IsNilpotent H)
  obtain ⟨m,⟨A⟩⟩ := nonempty_triangularAdjoint_of_nilpotent
    (GroupLieAlgebra (𝓘(ℝ,F.D.modelSpace)) F.D.carrier)
  exact intrinsic_exponential_contMDiff A F.ExpD F.isExpD

omit [H.IsCartanSubalgebra] in
theorem contMDiff_inclusionN (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ,F.N.modelSpace)) (𝓘(ℝ,E)) ∞ F.inclusionN := by
  let j := T.kernelIdeal.incl.comp F.N.equiv.symm.toLieHom
  apply contMDiff_of_exponential_compatibility F.isExpN hExp F.inclusionN
    F.closedN.continuous j.toLinearMap
  intro v
  change F.inclusionN (F.ExpN v) = Exp ((F.N.equiv.symm v : T.kernelIdeal) :
    GroupLieAlgebra (𝓘(ℝ,E)) G)
  have hv := F.compatibleN (F.N.equiv.symm v)
  simpa only [LieEquiv.apply_symm_apply] using hv

omit [H.IsCartanSubalgebra] in
theorem contMDiff_inclusionD (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ,F.D.modelSpace)) (𝓘(ℝ,E)) ∞ F.inclusionD := by
  let j := H.incl.comp F.D.equiv.symm.toLieHom
  apply contMDiff_of_exponential_compatibility F.isExpD hExp F.inclusionD
    F.closedD.continuous j.toLinearMap
  intro v
  change F.inclusionD (F.ExpD v) = Exp ((F.D.equiv.symm v : H) :
    GroupLieAlgebra (𝓘(ℝ,E)) G)
  have hv := F.compatibleD (F.D.equiv.symm v)
  simpa only [LieEquiv.apply_symm_apply] using hv

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
