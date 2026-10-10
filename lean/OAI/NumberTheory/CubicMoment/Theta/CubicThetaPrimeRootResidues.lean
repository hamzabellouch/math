import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootOperators

namespace OAI

/-! The fractional translations give an actual finite additive action on
sections, independent of the chosen representatives modulo the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootResidueOperator {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) : cubicThetaPrimeRootSections p ≃ₗ[ℂ] cubicThetaPrimeRootSections p :=
  cubicThetaPrimeRootOperator hp (residueRepresentative p r)

lemma cubicThetaPrimeRootResidueOperator_mk {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootResidueOperator hp (Ideal.Quotient.mk (modulus p) x)=
      cubicThetaPrimeRootOperator hp x := by
  apply cubicThetaPrimeRootOperator_congr
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (residueRepresentative_spec p (Ideal.Quotient.mk (modulus p) x)))

lemma cubicThetaPrimeRootResidueOperator_add {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootResidueOperator hp (r+s) F=
      cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootResidueOperator hp s F) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [←map_add,cubicThetaPrimeRootResidueOperator_mk,
    cubicThetaPrimeRootResidueOperator_mk,cubicThetaPrimeRootResidueOperator_mk]
  exact cubicThetaPrimeRootSectionTranslate_add hp x y F

@[simp] lemma cubicThetaPrimeRootResidueOperator_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootResidueOperator hp 0 F=F := by
  rw [←map_zero (Ideal.Quotient.mk (modulus p)),cubicThetaPrimeRootResidueOperator_mk]
  exact cubicThetaPrimeRootSectionTranslate_zero hp F

lemma cubicThetaPrimeRootResidueOperator_neg {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootResidueOperator hp (-r) (cubicThetaPrimeRootResidueOperator hp r F)=F := by
  rw [←cubicThetaPrimeRootResidueOperator_add,neg_add_cancel,
    cubicThetaPrimeRootResidueOperator_zero]

end CubicFirstMoment

end

end OAI
