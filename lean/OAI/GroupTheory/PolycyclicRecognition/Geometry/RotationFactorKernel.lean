import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorProduct
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistCharacter

namespace OAI

/-! # The nilpotent factor remains the kernel of the weight character -/

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
theorem weightCharacter_inclusionN (n : F.N.carrier) :
    F.weightCharacter (F.inclusionN n) = 1 := by
  obtain ⟨x,rfl⟩ := F.expN_surjective n
  exact F.weightCharacter_nilradical x

theorem inclusionN_range_eq_weightKernel :
    Set.range F.inclusionN = (F.weightCharacter.ker : Set G) := by
  ext g
  constructor
  · rintro ⟨n,rfl⟩
    exact F.weightCharacter_inclusionN n
  · intro hg
    obtain ⟨⟨n,d⟩,rfl⟩ := F.surjective g
    obtain ⟨h,rfl⟩ := F.expD_surjective d
    have hh : F.weightCharacter (Exp h) = 1 := by
      change F.weightCharacter (F.inclusionN n * F.inclusionD (F.ExpD (F.D.equiv h))) = 1 at hg
      rw [map_mul, F.weightCharacter_inclusionN, one_mul, F.compatibleD] at hg
      exact hg
    have hw : T.weightMap.rangeRestrict h = 0 :=
      (F.weightCharacter_exp h).symm.trans (congrArg Multiplicative.toAdd hh)
    have hz : T.weightMap h = 0 := congrArg Subtype.val hw
    let x : T.kernelIdeal := ⟨h,hz⟩
    refine ⟨n * F.ExpN (F.N.equiv x), ?_⟩
    change F.inclusionN (n * F.ExpN (F.N.equiv x)) =
      F.inclusionN n * F.inclusionD (F.ExpD (F.D.equiv h))
    rw [map_mul, F.compatibleN, F.compatibleD]

variable (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem weightCharacter_invariant_rotation (z) (g : G) :
    F.weightCharacter (F.factorCompactRotationAction hExp z g) = F.weightCharacter g := by
  exact character_invariant_of_factor_coordinates F.inclusionN F.inclusionD
    F.weightCharacter (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    F.expN_surjective F.surjective (fun z x => T.nilradicalRotation H z x)
    (fun z g => F.factorCompactRotationAction hExp z g) F.weightCharacter_nilradical
    (F.factorCompactRotationAction_formula hExp) z g

/-- The full vector-valued character survives the modification. -/
def rotationWeightCharacter :
    F.SmoothRotationalModification hExp →* Multiplicative T.weightMap.range :=
  rotationalTwistCharacter (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.weightCharacter
    (F.weightCharacter_invariant_rotation hExp)

theorem rotationWeightCharacter_kernel :
    (F.rotationWeightCharacter hExp).ker = (F.nilpotentFactorToRotation hExp).range := by
  apply SetLike.ext
  intro g
  change F.weightCharacter g.val.left = 1 ↔
    ∃ n, F.nilpotentFactorToRotation hExp n = g
  constructor
  · intro hg
    have hr : g.val.left ∈ Set.range F.inclusionN := by
      rw [F.inclusionN_range_eq_weightKernel]
      exact hg
    obtain ⟨n,hn⟩ := hr
    exact ⟨n,(F.smoothRotationalModificationHomeomorph hExp).injective hn⟩
  · rintro ⟨n,rfl⟩
    exact F.weightCharacter_inclusionN n

/-- Normality now follows from an actual homomorphism kernel. -/
theorem normal_nilpotentFactorToRotation :
    (F.nilpotentFactorToRotation hExp).range.Normal := by
  rw [← F.rotationWeightCharacter_kernel hExp]
  infer_instance

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
