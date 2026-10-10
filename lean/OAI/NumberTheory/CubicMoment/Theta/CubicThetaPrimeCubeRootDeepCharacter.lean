import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCoverDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootIwahoriConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSquareCharacter

namespace OAI

/-! A nontrivial diagonal character deep enough to normalize the actual
cubic root cover, for the intermediate-valuation cancellation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeSixthIwahori {p : Eisenstein} (g : cubicThetaPrimeIwahori (p^6)) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 6≠0)).trans g.property⟩

def cubicThetaPrimeSixthCubeIwahori {p : Eisenstein} (g : cubicThetaPrimeIwahori (p^6)) :
    cubicThetaPrimeIwahori (p^3) :=
  ⟨g.val,(pow_dvd_pow p (by decide : 3≤6)).trans g.property⟩

theorem cubicThetaPrimeSixthCharacter_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ g : cubicThetaPrimeIwahori (p^6),
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSixthIwahori g)≠1 := by
  obtain ⟨d,hd,hpd,hχ⟩ := cubicThetaPrime_primary_nontrivial hp
  let r : CubicThetaBottomRow :=
    ⟨3*p^6,d,dvd_mul_right 3 (p^6),hd,(primary_coprime_three hd).symm.mul_left hpd.pow_left⟩
  let g : cubicThetaPrimeIwahori (p^6) := ⟨r.completion,by
    have hc := congrArg CubicThetaBottomRow.c r.completion_row
    change r.completion.val 1 0=3*p^6 at hc
    change p^6∣r.completion.val 1 0
    rw [hc]
    exact dvd_mul_left (p^6) 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣g.val.val 0 0*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show g.val.val 0 0*d-1=g.val.val 0 1*g.val.val 1 0 by linear_combination hg]
    exact dvd_mul_of_dvd_right (cubicThetaPrimeSixthIwahori g).property _
  have hone : cubicSymbol p (g.val.val 0 0*d)=1 := by
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  rw [cubicSymbol_mul_upper hp.1] at hone
  intro htriv
  change cubicSymbol p (g.val.val 0 0)=1 at htriv
  rw [htriv,one_mul] at hone
  exact hχ hone


theorem cubicThetaPrimeCubeRootIwahoriImage_fundamental {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori (p^3)) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      ((fun x : CubicThetaPoint => g.val • x) '' cubicThetaPrimeCubeRootCoverDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootIwahoriEquiv g⁻¹)
  intro h x
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI
