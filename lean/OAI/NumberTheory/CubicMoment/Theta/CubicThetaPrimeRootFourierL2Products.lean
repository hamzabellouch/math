import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierL2Bounds

namespace OAI

/-! The completed Fourier projections retain the exact finite
orthogonal algebra and resolve the identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeRootFourierL2_product {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootFourierL2 hp k u)=
      if j=k then cubicThetaPrimeRootFourierL2 hp k u else 0 := by
  by_cases h : j=k
  · subst j
    simp only [ite_true]
    exact cubicThetaPrimeRootFourierL2_idempotent hp k u
  · simp only [ite_eq_right h]
    refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
      (isClosed_eq ((cubicThetaPrimeRootFourierL2 hp j).continuous.comp
        (cubicThetaPrimeRootFourierL2 hp k).continuous) continuous_const) ?_
    intro F
    rw [cubicThetaPrimeRootFourierL2_finite,cubicThetaPrimeRootFourierL2_finite]
    have he : cubicThetaPrimeRootFiniteFourier hp j (cubicThetaPrimeRootFiniteFourier hp k F)=0 := by
      apply Subtype.ext
      rw [cubicThetaPrimeRootFiniteFourier_val,cubicThetaPrimeRootFiniteFourier_val,
        cubicThetaPrimeRootFourierProjection_product,ite_eq_right h]
      rfl
    rw [he,map_zero]

theorem cubicThetaPrimeRootFourierL2_sum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    (∑ k : Residues p,cubicThetaPrimeRootFourierL2 hp k u)=u := by
  refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (continuous_finsetSum _ (fun k _ => (cubicThetaPrimeRootFourierL2 hp k).continuous))
      continuous_id) ?_
  intro F
  simp only [cubicThetaPrimeRootFourierL2_finite]
  rw [←map_sum]
  apply congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
  apply Subtype.ext
  change (cubicThetaPrimeRootFiniteSections hp).subtype
    (∑ k : Residues p,cubicThetaPrimeRootFiniteFourier hp k F)=F.val
  rw [map_sum]
  change (∑ k : Residues p,(cubicThetaPrimeRootFiniteFourier hp k F).val)=F.val
  simp only [cubicThetaPrimeRootFiniteFourier_val]
  exact cubicThetaPrimeRootFourierProjection_sum hp F.val

end CubicFirstMoment

end

end OAI
