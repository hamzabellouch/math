import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootLiftL2

namespace OAI

/-! The literal cubic-scale translations form the finite residue-group
action on the actual completed domain space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootTranslateL2_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp (x+y) u=
      cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootTranslateL2 hp y u) := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp (x+y)).continuous
      ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
        (cubicThetaPrimeCubeRootTranslateL2 hp y).continuous)) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootTranslateL2_finite,
    cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootSectionTranslate_add hp x y F.val

lemma cubicThetaPrimeCubeRootTranslateL2_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) : cubicThetaPrimeCubeRootTranslateL2 hp 0 u=u := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp 0).continuous continuous_id) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootSectionTranslate_zero hp F.val

lemma cubicThetaPrimeCubeRootTranslateL2_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p^3∣x-y) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp x u=cubicThetaPrimeCubeRootTranslateL2 hp y u := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp x).continuous
      (cubicThetaPrimeCubeRootTranslateL2 hp y).continuous) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact congrArg (fun T : cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p => T F.val)
    (cubicThetaPrimeCubeRootOperator_congr hp hxy)

def cubicThetaPrimeCubeRootResidueL2 {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ]
      cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  cubicThetaPrimeCubeRootTranslateL2 hp (residueRepresentative (p^3) r)

lemma cubicThetaPrimeCubeRootResidueL2_mk {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp (Ideal.Quotient.mk (modulus (p^3)) x) u=
      cubicThetaPrimeCubeRootTranslateL2 hp x u := by
  apply cubicThetaPrimeCubeRootTranslateL2_congr hp
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (residueRepresentative_spec (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)))

lemma cubicThetaPrimeCubeRootResidueL2_add {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues (p^3)) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp (r+s) u=
      cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootResidueL2 hp s u) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [←map_add,cubicThetaPrimeCubeRootResidueL2_mk,cubicThetaPrimeCubeRootResidueL2_mk,
    cubicThetaPrimeCubeRootResidueL2_mk,cubicThetaPrimeCubeRootTranslateL2_add]

lemma cubicThetaPrimeCubeRootResidueL2_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) : cubicThetaPrimeCubeRootResidueL2 hp 0 u=u := by
  rw [←map_zero (Ideal.Quotient.mk (modulus (p^3))),cubicThetaPrimeCubeRootResidueL2_mk,
    cubicThetaPrimeCubeRootTranslateL2_zero]

end CubicFirstMoment

end

end OAI
