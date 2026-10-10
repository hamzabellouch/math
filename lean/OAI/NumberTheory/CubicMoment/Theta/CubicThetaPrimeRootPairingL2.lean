import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSquareOrthogonal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMass

namespace OAI

/-! The literal root-cover integral is its L2 pairing; the original
and twice-dilated global Hilbert subspaces are orthogonal. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionPairing_L2 {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootFiniteSections hp) :
    inner ℂ (cubicThetaPrimeRootFiniteEmbedding hp F) (cubicThetaPrimeRootFiniteEmbedding hp G)=
      ∫ q, cubicThetaPrimeRootSectionPairing hp F.val G.val q ∂cubicThetaPrimeRootCoverMeasure hp := by
  change inner ℂ (F.property.toLp (cubicThetaPrimeRootSectionRepresentative hp F.val))
    (G.property.toLp (cubicThetaPrimeRootSectionRepresentative hp G.val))=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp,G.property.coeFn_toLp] with q hF hG
  rw [hF,hG]
  have he := cubicThetaPrimeRootSectionPairing_apply hp F.val G.val (cubicThetaPrimeRootBorelSection hp q)
  rw [cubicThetaPrimeRootBorelSection_rightInverse hp q] at he
  simpa only [RCLike.inner_apply',Complex.star_def,cubicThetaPrimeRootSectionRepresentative] using he.symm

lemma cubicThetaPrimeRootSmoothWeyl_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F))
      (cubicThetaPrimeRootWeylL2 hp
        (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp G)))=0 := by
  rw [cubicThetaPrimeRootWeylL2_finite,cubicThetaPrimeRootSectionPairing_L2,
    cubicThetaPrimeRootSectionPairing_unfold]
  exact cubicThetaPrimeRootSquare_pair_integral_zero hp F.val G.val

theorem cubicThetaPrimeRootLiftWeyl_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp v))=0) ?_ ?_ u v
  · apply isClosed_eq _ continuous_const
    exact ((cubicThetaPrimeRootLiftL2 hp).continuous.comp continuous_fst).inner
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp
        ((cubicThetaPrimeRootLiftL2 hp).continuous.comp continuous_snd))
  · intro F G
    simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
      LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
    rw [inner_smul_left,
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
      cubicThetaPrimeRootSmoothWeyl_orthogonal,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
