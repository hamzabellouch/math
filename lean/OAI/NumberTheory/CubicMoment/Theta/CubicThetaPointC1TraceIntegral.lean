import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Pairing

namespace OAI

/-! The gradient trace adjoint on the actual finite cover, obtained
from the pointwise isometry identity and justified finite integration. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPointC1Trace_gradient_integral {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hGc : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F))
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hi := cubicThetaPointC1Pair_integrable F G hF hGc
  simp_rw [cubicThetaPointC1Trace_gradient_point hp F G hG,tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeComplexSheet_integrable hp hi t),
    cubicThetaPrimeCubeComplexSheetIntegral hp hi,tsum_fintype]

lemma cubicThetaPointC1Pair_flip (F G : cubicThetaPointC1) (S : Set CubicThetaPoint) :
    star (∫ x in S,inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure)=
    ∫ x in S,inner ℂ (cubicThetaPointC1Gradient x F)
      (cubicThetaPointC1Gradient x G) ∂cubicThetaPointMeasure := by
  have he := (integral_conj (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x G)
    (cubicThetaPointC1Gradient x F)) (μ:=cubicThetaPointMeasure.restrict S)).symm
  change star (∫ x in S,inner ℂ (cubicThetaPointC1Gradient x G)
    (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure)=
    ∫ x in S,(starRingEnd ℂ) (inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F)) ∂cubicThetaPointMeasure at he
  simpa only [inner_conj_symm] using he

theorem cubicThetaPointC1Trace_gradient_integral_left {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hGc : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F)) (cubicThetaPointC1Gradient x G)
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x F) (cubicThetaPointC1Gradient x G) ∂cubicThetaPointMeasure := by
  have he := congrArg star (cubicThetaPointC1Trace_gradient_integral hp F G hG hF hGc)
  rwa [cubicThetaPointC1Pair_flip,cubicThetaPointC1Pair_flip] at he

end CubicFirstMoment

end

end OAI
