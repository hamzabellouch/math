import OAI.NumberTheory.CubicMoment.Estimates.ElementaryDischargedMains
import OAI.NumberTheory.CubicMoment.Estimates.MontgomeryVaughanProof

namespace OAI

/-! All exact main statements with the elementary and ordinary mean-value inputs proved. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_character_and_metaplectic_inputs
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate) (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_remaining_inputs hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley
    montgomeryVaughanBound_proved ordinaryMeanValueConstant_pos.le hVor hF hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
