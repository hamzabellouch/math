import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootSections

namespace OAI

/-! The fractional translations give an actual finite additive action on
sections, independent of the chosen representatives modulo the cube. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootResidueOperator {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) : cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p :=
  cubicThetaPrimeCubeRootOperator hp (residueRepresentative (p^3) r)

lemma cubicThetaPrimeCubeRootResidueOperator_mk {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootResidueOperator hp (Ideal.Quotient.mk (modulus (p^3)) x)=
      cubicThetaPrimeCubeRootOperator hp x := by
  apply cubicThetaPrimeCubeRootOperator_congr
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (residueRepresentative_spec (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)))

lemma cubicThetaPrimeCubeRootResidueOperator_add {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues (p^3)) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootResidueOperator hp (r+s) F=
      cubicThetaPrimeCubeRootResidueOperator hp r (cubicThetaPrimeCubeRootResidueOperator hp s F) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [←map_add,cubicThetaPrimeCubeRootResidueOperator_mk,
    cubicThetaPrimeCubeRootResidueOperator_mk,cubicThetaPrimeCubeRootResidueOperator_mk]
  exact cubicThetaPrimeCubeRootSectionTranslate_add hp x y F

@[simp] lemma cubicThetaPrimeCubeRootResidueOperator_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootResidueOperator hp 0 F=F := by
  rw [←map_zero (Ideal.Quotient.mk (modulus (p^3))),cubicThetaPrimeCubeRootResidueOperator_mk]
  exact cubicThetaPrimeCubeRootSectionTranslate_zero hp F

lemma cubicThetaPrimeCubeRootResidueOperator_neg {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootResidueOperator hp (-r) (cubicThetaPrimeCubeRootResidueOperator hp r F)=F := by
  rw [←cubicThetaPrimeCubeRootResidueOperator_add,neg_add_cancel,
    cubicThetaPrimeCubeRootResidueOperator_zero]

end CubicFirstMoment

end

end OAI
