import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAbelianizedDimension
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

namespace OAI

/-! # Detecting nilpotent finite dimension in actual first homology -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {G : Type} [Group G]

def integralH1AbelianizationEquiv :
    groupHomology.H1 (integralTrivialCoefficient G) ≃ₗ[ℤ] Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (integralTrivialCoefficient G)).toIntLinearEquiv.trans
    (TensorProduct.rid ℤ _)

def rationalH1AbelianizationEquiv :
    (ℚ ⊗[ℤ] groupHomology.H1 (integralTrivialCoefficient G)) ≃ₗ[ℚ]
      RationalAbelianSpace (Abelianization G) :=
  (integralH1AbelianizationEquiv (G := G)).baseChange ℤ ℚ _ _

theorem rationalH1_finite_iff_abelianization_finite :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology.H1 (integralTrivialCoefficient G)) ↔
      Module.Finite ℚ (RationalAbelianSpace (Abelianization G)) := by
  let e := rationalH1AbelianizationEquiv (G := G)
  constructor
  · intro h
    let := h
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · intro h
    let := h
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

theorem nilpotent_finiteDimension_iff_rationalH1_finite
    [Group.IsNilpotent G] [Countable G] (htf : HasNoNontrivialTorsion G) :
    HasFiniteIntegralCohomologicalDimension G ↔
      Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology.H1 (integralTrivialCoefficient G)) := by
  rw [rationalH1_finite_iff_abelianization_finite]
  constructor
  · rintro ⟨d, hd⟩
    let := hd
    apply Module.rank_lt_aleph0_iff.mp
    rw [rationalAbelianSpace_rank]
    exact (nilpotent_abelian_quotient_rank_le d (Abelianization.of (G := G))
      (QuotientGroup.mk'_surjective (commutator G))).trans_lt Cardinal.natCast_lt_aleph0
  · intro h
    let := h
    exact nilpotent_finiteDimension_of_finite_abelianization htf

end PolycyclicRecognition

end

end OAI
