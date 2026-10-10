import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootTranslationL2

namespace OAI

/-! The geometric root-group and Weyl relations persist on the actual
Hilbert completion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootResidueL2_add {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues p) (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    cubicThetaPrimeRootResidueL2 hp (r+s) u=
      cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootResidueL2 hp s u) := by
  refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeRootResidueL2 hp (r+s)).continuous
      ((cubicThetaPrimeRootResidueL2 hp r).continuous.comp
        (cubicThetaPrimeRootResidueL2 hp s).continuous)) ?_
  intro F
  rw [cubicThetaPrimeRootResidueL2_finite,cubicThetaPrimeRootResidueL2_finite,
    cubicThetaPrimeRootResidueL2_finite]
  apply congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeRootResidueOperator_add hp r s F.val

lemma cubicThetaPrimeRootResidueL2_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeRootAutomorphicL2 hp) : cubicThetaPrimeRootResidueL2 hp 0 u=u := by
  refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeRootResidueL2 hp 0).continuous continuous_id) ?_
  intro F
  rw [cubicThetaPrimeRootResidueL2_finite]
  apply congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeRootResidueOperator_zero hp F.val

theorem cubicThetaPrimeRootWeylL2_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeRootWeylL2 hp) := by
  intro u
  refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeRootWeylL2 hp).continuous.comp
      (cubicThetaPrimeRootWeylL2 hp).continuous) continuous_id) ?_
  intro F
  rw [cubicThetaPrimeRootWeylL2_finite,cubicThetaPrimeRootWeylL2_finite]
  apply congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeRootWeylSection_involutive hp F.val

end CubicFirstMoment

end

end OAI
