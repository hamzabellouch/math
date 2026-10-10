import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorLifts

namespace OAI

/-! # Exponential compatibility of the factors in the rotational graph -/

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
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

omit [H.IsCartanSubalgebra] in
include hExp in
theorem mfderiv_inclusionN_at_one (x : T.kernelIdeal) :
    mfderiv (𝓘(ℝ,F.N.modelSpace)) (𝓘(ℝ,E)) F.inclusionN 1 (F.N.equiv x) =
      (show E from (x : GroupLieAlgebra (𝓘(ℝ,E)) G)) := by
  let j := T.kernelIdeal.incl.comp F.N.equiv.symm.toLieHom
  have he (v : F.N.modelSpace) : F.inclusionN (F.ExpN v) = Exp (j v) := by
    change F.inclusionN (F.ExpN v) = Exp (F.N.equiv.symm v)
    have h := F.compatibleN (F.N.equiv.symm v)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier =>
      F.inclusionN (F.ExpN y)) (F.N.equiv.apply_symm_apply v)).symm.trans h
  have hd := mfderiv_eq_of_exponential_compatibility F.isExpN hExp F.inclusionN
    ((F.contMDiff_inclusionN hExp).mdifferentiable (by simp)) j.toLinearMap he (F.N.equiv x)
  change mfderiv (𝓘(ℝ,F.N.modelSpace)) (𝓘(ℝ,E)) F.inclusionN 1 (F.N.equiv x) =
    (F.N.equiv.symm (F.N.equiv x) : GroupLieAlgebra (𝓘(ℝ,E)) G) at hd
  rw [LieEquiv.symm_apply_apply] at hd
  exact hd

omit [H.IsCartanSubalgebra] in
include hExp in
theorem mfderiv_inclusionD_at_one (x : H) :
    mfderiv (𝓘(ℝ,F.D.modelSpace)) (𝓘(ℝ,E)) F.inclusionD 1 (F.D.equiv x) =
      (show E from (x : GroupLieAlgebra (𝓘(ℝ,E)) G)) := by
  let j := H.incl.comp F.D.equiv.symm.toLieHom
  have he (v : F.D.modelSpace) : F.inclusionD (F.ExpD v) = Exp (j v) := by
    change F.inclusionD (F.ExpD v) = Exp (F.D.equiv.symm v)
    have h := F.compatibleD (F.D.equiv.symm v)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier =>
      F.inclusionD (F.ExpD y)) (F.D.equiv.apply_symm_apply v)).symm.trans h
  have hd := mfderiv_eq_of_exponential_compatibility F.isExpD hExp F.inclusionD
    ((F.contMDiff_inclusionD hExp).mdifferentiable (by simp)) j.toLinearMap he (F.D.equiv x)
  change mfderiv (𝓘(ℝ,F.D.modelSpace)) (𝓘(ℝ,E)) F.inclusionD 1 (F.D.equiv x) =
    (F.D.equiv.symm (F.D.equiv x) : GroupLieAlgebra (𝓘(ℝ,E)) G) at hd
  rw [LieEquiv.symm_apply_apply] at hd
  exact hd


end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
