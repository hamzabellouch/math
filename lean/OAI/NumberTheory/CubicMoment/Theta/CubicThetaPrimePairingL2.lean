import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftL2

namespace OAI

/-! The finite-cover integral pairing is the actual L2 inner product.
Original sections are orthogonal to their prime Atkin translates. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeSectionPairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) : CubicThetaPrimeCover hp → ℂ :=
  Quotient.lift (fun x : CubicThetaPoint => inner ℂ (F.val x) (G.val x)) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg]
    simpa only [RCLike.inner_apply',Complex.star_def] using
      cubicThetaPrimeSectionPair_invariant hp F G g y)

lemma cubicThetaPrimeSectionPairing_apply {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionPairing hp F G (cubicThetaPrimeCoverMap hp x)=
      inner ℂ (F.val x) (G.val x) := rfl

lemma cubicThetaPrimeSectionPairing_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) : Continuous (cubicThetaPrimeSectionPairing hp F G) := by
  apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact F.val.continuous.inner G.val.continuous

lemma cubicThetaPrimeSectionPairing_L2 {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeFiniteSections hp) :
    inner ℂ (cubicThetaPrimeFiniteValue hp F) (cubicThetaPrimeFiniteValue hp G)=
      ∫ q, cubicThetaPrimeSectionPairing hp F.val G.val q ∂cubicThetaPrimeCoverMeasure hp := by
  change inner ℂ (F.property.toLp (cubicThetaPrimeSectionRepresentative hp F.val))
    (G.property.toLp (cubicThetaPrimeSectionRepresentative hp G.val))=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp,G.property.coeFn_toLp] with q hF hG
  rw [hF,hG]
  have he := cubicThetaPrimeSectionPairing_apply hp F.val G.val (cubicThetaPrimeBorelSection hp q)
  rw [cubicThetaPrimeBorelSection_rightInverse hp q] at he
  exact he.symm

lemma cubicThetaPrimeSectionPairing_unfold {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) :
    (∫ q, cubicThetaPrimeSectionPairing hp F G q ∂cubicThetaPrimeCoverMeasure hp)=
      ∫ x in cubicThetaPrimeCoverDomain hp, inner ℂ (F.val x) (G.val x) ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCoverMeasure]
  exact integral_map_of_stronglyMeasurable
    (cubicThetaPrimeCoverMap_open hp).continuous.measurable
    (cubicThetaPrimeSectionPairing_continuous hp F G).stronglyMeasurable

theorem cubicThetaPrimeSmoothAtkin_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeSmoothRestriction hp F))
      (cubicThetaPrimeAtkinL2 hp
        (cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeSmoothRestriction hp G)))=0 := by
  rw [cubicThetaPrimeAtkinL2_finite]
  change inner ℂ (cubicThetaPrimeFiniteValue hp (cubicThetaPrimeSmoothRestriction hp F))
    (cubicThetaPrimeFiniteValue hp (cubicThetaPrimeFiniteAtkin hp
      (cubicThetaPrimeSmoothRestriction hp G)))=0
  rw [cubicThetaPrimeSectionPairing_L2,cubicThetaPrimeSectionPairing_unfold]
  change (∫ x in cubicThetaPrimeCoverDomain hp,
    inner ℂ (F.val.val x) (G.val.val (cubicThetaPrimeAtkinMatrix hp • x))
      ∂cubicThetaPointMeasure)=0
  simpa only [RCLike.inner_apply',Complex.star_def] using
    cubicThetaPrimeOriginalAtkinPair_integral_zero hp F.val G.val

end CubicFirstMoment

end

end OAI
