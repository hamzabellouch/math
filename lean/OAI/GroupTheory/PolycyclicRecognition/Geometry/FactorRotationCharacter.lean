import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegratedCartanRotations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightRotationCharacter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactRotationalTwist

namespace OAI

/-! # The invariant compact character for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/- The actual quotient character followed by its compact rotational part. -/
def rotationCharacter : G →* realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H :=
  T.liftRotationCharacter H F.weightCharacter

theorem continuous_rotationCharacter : Continuous F.rotationCharacter :=
  T.continuous_liftRotationCharacter H F.weightCharacter F.continuousWeightCharacter

theorem rotationCharacter_exp (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    F.rotationCharacter (Exp x) =
      T.weightRotationCharacter H (Multiplicative.ofAdd (T.weightMap.rangeRestrict x)) := by
  exact congrArg (T.weightRotationCharacter H) (Multiplicative.ext (F.weightCharacter_exp x))

theorem rotationCharacter_cartan (h : H) :
    F.rotationCharacter (Exp h) = realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h :=
  (F.rotationCharacter_exp h).trans (T.weightRotationCharacter_cartan H h)

omit [H.IsCartanSubalgebra] in
theorem weightCharacter_nilradical (x : T.kernelIdeal) :
    F.weightCharacter (F.inclusionN (F.ExpN (F.N.equiv x))) = 1 := by
  apply Multiplicative.ext
  exact (congrArg (fun g => (F.weightCharacter g).toAdd) (F.compatibleN x)).trans
    ((F.weightCharacter_exp x).trans (Subtype.ext x.property))

theorem rotationCharacter_nilradical (x : T.kernelIdeal) :
    F.rotationCharacter (F.inclusionN (F.ExpN (F.N.equiv x))) = 1 :=
  (congrArg (T.weightRotationCharacter H) (F.weightCharacter_nilradical x)).trans
    (T.weightRotationCharacter H).map_one

theorem rotationCharacter_invariant
    (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
    (hβ : ∀ z (x : T.kernelIdeal) d,
      β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
        F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d) :
    ∀ z g, F.rotationCharacter (β z g) = F.rotationCharacter g := by
  exact character_invariant_of_factor_coordinates F.inclusionN F.inclusionD
    F.rotationCharacter (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    F.expN_surjective F.surjective (fun z x => T.nilradicalRotation H z x)
    (fun z g => β z g) F.rotationCharacter_nilradical hβ

/- Both ingredients of the rotational modification now exist for the
original group, with the exact invariance required by the graph subgroup. -/
include T in
theorem exists_invariant_compact_rotations (hExp : IsGroupExponential Exp) :
    ∃ β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G,
      Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × G => β p.1 p.2) ∧
      ∀ z g, F.rotationCharacter (β z g) = F.rotationCharacter g := by
  let h := F.exists_compact_rotation_action hExp
  exact ⟨h.choose,h.choose_spec.1,F.rotationCharacter_invariant h.choose h.choose_spec.2⟩

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
