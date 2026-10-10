import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProperAction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaCharacter

namespace OAI

/-! Arithmetic separation of the high cusp. Two points above height one
can be equivalent under the principal group only by the actual period
lattice 3 times the Eisenstein integers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobius_height_product_le (g : SL(2,Eisenstein))
    (hc : g 1 0≠0) {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaMobius (cubicThetaFullComplex g) p).2*p.2≤1 := by
  have hD := cubicThetaMobius_denominator_pos (cubicThetaFullComplex g) hp
  have hN := one_le_norm hc
  have hbound : p.2^2≤cubicThetaMobiusDenominator (cubicThetaFullComplex g) p := by
    change p.2^2≤Complex.normSq (((g 1 0:Eisenstein):ℂ)*p.1+((g 1 1:Eisenstein):ℂ))+
      norm (g 1 0)*p.2^2
    nlinarith [Complex.normSq_nonneg (((g 1 0:Eisenstein):ℂ)*p.1+((g 1 1:Eisenstein):ℂ)),
      mul_le_mul_of_nonneg_right hN (sq_nonneg p.2)]
  change p.2/cubicThetaMobiusDenominator (cubicThetaFullComplex g) p*p.2≤1
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).mpr
  nlinarith

lemma cubicThetaMobius_high_overlap (g : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 1<p.2) (hq : 1<(cubicThetaMobius (cubicThetaFullComplex g) p).2) : g 1 0=0 := by
  by_contra hc
  have h := cubicThetaMobius_height_product_le g hc (lt_trans zero_lt_one hp)
  have hp0 := lt_trans zero_lt_one hp
  nlinarith

lemma cubicThetaPrincipal_parabolic (g : cubicThetaPrincipalGroup) (hc : g.val 1 0=0) :
    g.val 0 0=1 ∧ g.val 1 1=1 := by
  have hu := cubicThetaPrincipalGroup_column_coprime g
  rw [hc] at hu
  have ha := primary_unit_eq_one (isCoprime_zero_right.mp hu)
    (cubicThetaPrincipalGroup_diagonal_primary g).1
  have hd := cubicThetaPrincipalGroup_det g
  rw [ha,hc,one_mul,mul_zero,sub_zero] at hd
  exact ⟨ha,hd⟩

lemma cubicThetaPrincipal_high_translation (g : cubicThetaPrincipalGroup)
    {p : CubicThetaPoint} (hp : 1<p.val.2) (hq : 1<(g • p).val.2) :
    ∃ w : Eisenstein, (g • p).val=(p.val.1+(3:ℂ)*(w:ℂ),p.val.2) := by
  have hq' : 1<(cubicThetaMobius (cubicThetaFullComplex g.val) p.val).2 := hq
  have hc := cubicThetaMobius_high_overlap g.val hp hq'
  obtain ⟨ha,hd⟩ := cubicThetaPrincipal_parabolic g hc
  obtain ⟨w,hw⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
  refine ⟨w,?_⟩
  change cubicThetaMobius (cubicThetaFullComplex g.val) p.val=_
  have ha' : cubicThetaFullComplex g.val 0 0=1 := congrArg (fun z : Eisenstein => (z:ℂ)) ha
  have hd' : cubicThetaFullComplex g.val 1 1=1 := congrArg (fun z : Eisenstein => (z:ℂ)) hd
  have hc' : cubicThetaFullComplex g.val 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) hc
  have hb' : cubicThetaFullComplex g.val 0 1=(3:ℂ)*(w:ℂ) := by
    change ((g.val 0 1:Eisenstein):ℂ)=(3:ℂ)*(w:ℂ)
    have he := congrArg (fun z : Eisenstein => (z:ℂ)) hw
    change ((g.val 0 1:Eisenstein):ℂ)=((3:Eisenstein):ℂ)*(w:ℂ) at he
    exact he
  simp [cubicThetaMobius,cubicThetaMobiusDenominator,cubicThetaMobiusNumerator,ha',hd',hc',hb']

end CubicFirstMoment

end

end OAI
