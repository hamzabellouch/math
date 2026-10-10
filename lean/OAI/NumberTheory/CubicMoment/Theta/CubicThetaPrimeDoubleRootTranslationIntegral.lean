import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootOrthogonal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootBruhat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckePairing

namespace OAI

/-! Nontrivial translations at the intermediate denominator have zero
integral correlation, by the proved Bruhat identity and character cancellation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeDoubleRootWeylSection hp
      (cubicThetaPrimeDoubleRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicSymbol (p^2) (3*y) • cubicThetaPrimeDoubleRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeDoubleRootElement hp y • (cubicThetaPrimeDoubleRootWeylElement hp • z))=
    cubicSymbol (p^2) (3*y)*(cubicThetaInversionSection F).val (cubicThetaPrimeDoubleRootElement hp (-x) • z)
  have he := cubicThetaPrimeDoubleRootBruhat_section hp x y hxy F (cubicThetaPrimeDoubleRootElement hp (-x) • z)
  have hx : cubicThetaPrimeDoubleRootElement hp x • (cubicThetaPrimeDoubleRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeDoubleRootElement_add,add_neg_cancel,cubicThetaPrimeDoubleRootElement_zero,one_smul]
  rw [hx] at he
  exact he

theorem cubicThetaPrimeDoubleRoot_translation_integral_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have hpx : IsCoprime p x := hp.2.coprime_iff_not_dvd.mpr hx
  have hp9 : IsCoprime p (9:Eisenstein) := by
    simpa only [show (3:Eisenstein)^2=9 by norm_num] using (primary_coprime_three hp.1).pow_right (n:=2)
  have hcop : IsCoprime (p^2) (9*x) := (hp9.mul_right hpx).pow_left
  obtain ⟨a,y,hxy⟩ := hcop
  have hd : p^2∣9*y*x-1 := ⟨-a,by linear_combination hxy⟩
  let A := cubicThetaPrimeRootSectionRestrict (p:=p^2) F
  let B := cubicThetaPrimeDoubleRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)
  let H := cubicThetaPrimeDoubleRootWeylSection hp A
  let J := cubicThetaPrimeRootSectionRestrict (p:=p^2) (cubicThetaInversionSection G)
  let K := cubicThetaPrimeDoubleRootSectionTranslate hp (-y) J
  let c := cubicSymbol (p^2) (3*x)
  have hBruhat : cubicThetaPrimeDoubleRootWeylSection hp B=c • K :=
    cubicThetaPrimeDoubleRootWeyl_translated_global hp y x hd G
  have hH (z : CubicThetaPoint) : H.val (cubicThetaPrimeDoubleRootElement hp (-y) • z)=H.val z :=
    congrArg (fun T : cubicThetaPrimeDoubleRootSections p => T.val z)
      (cubicThetaPrimeDoubleRootWeyl_global_translate hp (-y) F)
  have hpair : (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*K.val z ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*J.val z ∂cubicThetaPointMeasure := by
    change (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*
      J.val (cubicThetaPrimeDoubleRootElement hp (-y) • z) ∂cubicThetaPointMeasure)=_
    have he := cubicThetaPrimeDoubleRoot_pair_translation hp (-y) H J
    simpa only [hH] using he
  have hzero : (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*J.val z
      ∂cubicThetaPointMeasure)=0 := by
    have he := congrArg star (cubicThetaPrimeDoubleRootWeyl_pair_zero hp (cubicThetaInversionSection G) F)
    rw [cubicThetaComplexPair_flip,star_zero] at he
    exact he
  calc
    _ = ∫ z in cubicThetaPrimeDoubleRootDomain hp,
        star ((cubicThetaPrimeDoubleRootWeylSection hp A).val z)*
          (cubicThetaPrimeDoubleRootWeylSection hp B).val z ∂cubicThetaPointMeasure :=
      (cubicThetaPrimeDoubleRoot_pair_weyl hp A B).symm
    _ = ∫ z in cubicThetaPrimeDoubleRootDomain hp,
        c*(star (H.val z)*K.val z) ∂cubicThetaPointMeasure := by
      rw [hBruhat]
      apply integral_congr_ae
      filter_upwards with z
      change star (H.val z)*(c*K.val z)=c*(star (H.val z)*K.val z)
      ring
    _ = c*(∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*K.val z
        ∂cubicThetaPointMeasure) := integral_const_mul c _
    _ = 0 := by rw [hpair,hzero,mul_zero]

end CubicFirstMoment

end

end OAI
