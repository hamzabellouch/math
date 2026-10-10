import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SmallCoefficientRing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexTraceRetract
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerProjectiveCoefficientDimension
import Mathlib.GroupTheory.Schreier

namespace OAI

/-! # The small coefficient ring over finite-index subgroups

Relative coset indicators provide an actual trace-one element. Restriction to
an integer-finite-dimensional subgroup therefore bounds the dimension of the
ring over the larger subgroup, without requiring normality.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G] (J : Subgroup G) (hJ : J.FG)
variable (N : Subgroup J) (hN : N.FG)

def smallCoefficientRelativeTransversal : SmallCoefficientRing G :=
  ⟨fun x => if smallCoefficientFeature G (Sum.inr ⟨⟨J, hJ⟩, ⟨N, hN⟩⟩, 1) x then 1 else 0,
    booleanStepRing_coordinate _ _⟩

@[simp]
theorem smallCoefficientRelativeTransversal_apply (x : G) :
    (smallCoefficientRelativeTransversal G J hJ N hN).val x =
      if subgroupRightPart J x ∈ N then 1 else 0 := by
  simp [smallCoefficientRelativeTransversal, smallCoefficientFeature]

theorem smallCoefficientRelativeTransversal_invariant (n : N) :
    ((n : J) : G) • smallCoefficientRelativeTransversal G J hJ N hN =
      smallCoefficientRelativeTransversal G J hJ N hN := by
  apply Subtype.ext
  funext x
  simp only [smallCoefficientRing_smul_apply, smallCoefficientRelativeTransversal_apply]
  have hp : subgroupRightPart J (((n : J) : G)⁻¹ * x) =
      (n : J)⁻¹ * subgroupRightPart J x := subgroupRightPart_mul J (n : J)⁻¹ x
  rw [hp, N.mul_mem_cancel_left (N.inv_mem n.property)]

theorem rightCoset_representative_mul_mem_iff (c : subgroupRightCosets N) (x : J) :
    subgroupRightRepresentative N c * x ∈ N ↔ c = subgroupRightCoset N x⁻¹ := by
  rw [← subgroupRightRepresentative_coset N c]
  constructor
  · intro h
    apply Quotient.sound
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev] using N.inv_mem h
  · intro h
    have hh := (QuotientGroup.rightRel_apply).mp (Quotient.exact h)
    simpa [mul_inv_rev] using N.inv_mem hh

local instance : MulSemiringAction J (SmallCoefficientRing G) :=
  MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype

theorem smallCoefficientRelativeTransversal_trace_one
    [Fintype (subgroupRightCosets N)] :
    (∑ c : subgroupRightCosets N, ((subgroupRightRepresentative N c : J)⁻¹ : J) •
      smallCoefficientRelativeTransversal G J hJ N hN) = 1 := by
  let := MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype
  apply Subtype.ext
  funext x
  change ((SmallCoefficientRing G).subtype
    (∑ c : subgroupRightCosets N, (subgroupRightRepresentative N c)⁻¹ •
      smallCoefficientRelativeTransversal G J hJ N hN)) x = 1
  rw [map_sum, Finset.sum_apply]
  change (∑ c : subgroupRightCosets N, (((subgroupRightRepresentative N c)⁻¹ : J) •
    smallCoefficientRelativeTransversal G J hJ N hN).val x) = 1
  have hp (c : subgroupRightCosets N) :
      (((subgroupRightRepresentative N c)⁻¹ : J) •
        smallCoefficientRelativeTransversal G J hJ N hN).val x =
      if c = subgroupRightCoset N (subgroupRightPart J x)⁻¹ then 1 else 0 := by
    change ((((subgroupRightRepresentative N c)⁻¹ : J) : G) •
      smallCoefficientRelativeTransversal G J hJ N hN).val x = _
    rw [smallCoefficientRing_smul_apply, smallCoefficientRelativeTransversal_apply]
    simp only [Subgroup.coe_inv, inv_inv]
    rw [subgroupRightPart_mul, rightCoset_representative_mul_mem_iff]
    split_ifs <;> rfl
  simp_rw [hp]
  simp

include hJ hN in
theorem smallCoefficient_finiteIndex_dimension_le [Countable G] [N.FiniteIndex]
    (d : ℕ) (hd : HasProjectiveDimensionLE (trivialIntegral N) d) :
    HasProjectiveDimensionLE (Rep.res J.subtype (smallCoefficientRepresentation G)) d := by
  let := MulSemiringAction.compHom (SmallCoefficientRing G) J.subtype
  let : Finite (subgroupRightCosets N) :=
    Finite.of_equiv (J ⧸ N) (QuotientGroup.quotientRightRelEquivQuotientLeftRel N).symm
  let := Fintype.ofFinite (subgroupRightCosets N)
  apply relativeTrace_dimension_le N (smallCoefficientRelativeTransversal G J hJ N hN)
    (smallCoefficientRelativeTransversal_invariant G J hJ N hN) d
    (smallCoefficientRelativeTransversal_trace_one G J hJ N hN)
  exact integerProjectiveCoefficient_dimension_le _ d hd

end PolycyclicRecognition

end

end OAI
