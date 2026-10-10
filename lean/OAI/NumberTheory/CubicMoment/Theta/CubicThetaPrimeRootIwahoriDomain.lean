import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootIwahoriConjugation

namespace OAI

/-! The integral Iwahori normalizer sends the actual root-cover
fundamental domain to another fundamental domain of the same subgroup. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeRootIwahoriImage_fundamental {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun x : CubicThetaPoint => g.val • x) '' cubicThetaPrimeRootCoverDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootIwahoriEquiv g⁻¹)
  intro h x
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI
