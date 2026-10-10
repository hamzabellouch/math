import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCubes
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantContinuation

namespace OAI

/-! Exact ideal reindexing and Euler factor of the inverted-cusp
constant coefficient, derived from its actual finite character sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInvertedConstantWeight (s : ℂ) (c : Eisenstein) : ℂ :=
  if primary c then cubicThetaInvertedConstantGauss c*(norm c:ℂ)^(-s) else 0

def cubicThetaInvertedConstantDirichlet (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaInvertedConstantWeight s c

lemma cubicThetaInvertedConstantWeight_support (s : ℂ) :
    Function.support (cubicThetaInvertedConstantWeight s) ⊆
      {c : Eisenstein | primary c ∧ ∃ j : Eisenstein, j^3=c} := by
  intro c hc
  by_cases hp : primary c
  · refine ⟨hp,?_⟩
    by_contra hcb
    exact hc (by simp [cubicThetaInvertedConstantWeight,hp,
      cubicThetaInvertedConstantGauss_eq hp,hcb])
  · exact False.elim (hc (by simp [cubicThetaInvertedConstantWeight,hp]))

lemma cubicThetaInvertedConstantWeight_cube (s : ℂ) (ν : CubicThetaUnramifiedIdeal) :
    cubicThetaInvertedConstantWeight s (cubicThetaPrimaryCubeMap ν).val=
      cubicThetaIdealDensity ν.val*(idealExponentNorm ν.val:ℂ)^(-(3*s-3)) := by
  have hp := (cubicThetaPrimaryCubeMap ν).property
  rw [cubicThetaInvertedConstantWeight,ite_eq_left hp.1,
    cubicThetaInvertedConstantGauss_eq hp.1,ite_eq_left hp.2,
    cubicThetaPrimaryCube_units,cubicThetaPrimaryCube_norm,cubicThetaIdealDensity,
    Complex.ofReal_pow]
  have hN := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν.val).ne'
  have he : ((idealExponentNorm ν.val:ℂ)^3)^(-s)=
      (idealExponentNorm ν.val:ℂ)^(-3*s) := by
    rw [←Complex.cpow_nat_mul' (n:=3)
      (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν.val).le]; nlinarith [Real.pi_pos])
      (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν.val).le]; nlinarith [Real.pi_pos])]
    congr 1
    ring
  rw [he,show -(3*s-3)=(3:ℂ)+(-3*s) by ring,Complex.cpow_add _ _ hN,
    show (idealExponentNorm ν.val:ℂ)^(3:ℂ)=(idealExponentNorm ν.val:ℂ)^3 from
      Complex.cpow_natCast _ 3]
  field_simp

lemma cubicThetaInvertedConstantDirichlet_ideal (s : ℂ) :
    cubicThetaInvertedConstantDirichlet s=
      ∑' ν : CubicThetaUnramifiedIdeal,
        cubicThetaIdealDensity ν.val*(idealExponentNorm ν.val:ℂ)^(-(3*s-3)) := by
  calc
    _ = ∑' c : CubicThetaPrimaryCube, cubicThetaInvertedConstantWeight s c.val :=
      (tsum_subtype_eq_of_support_subset (cubicThetaInvertedConstantWeight_support s)).symm
    _ = ∑' ν : CubicThetaUnramifiedIdeal,
        cubicThetaInvertedConstantWeight s (cubicThetaPrimaryCubeMap ν).val :=
      (cubicThetaPrimaryCubeEquiv.tsum_eq _).symm
    _ = _ := tsum_congr (cubicThetaInvertedConstantWeight_cube s)

lemma cubicThetaInvertedConstantDirichlet_difference {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaInvertedConstantDirichlet s=
      normDirichletSeries cubicThetaIdealDensity idealExponentNorm (3*s-3)-
        cubicThetaRamifiedDensitySeries (3*s-3) := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  let f (ν : EisensteinIdealExponent) :=
    cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-(3*s-3))
  let g (ν : EisensteinIdealExponent) :=
    cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*(idealExponentNorm ν:ℂ)^(-(3*s-3))
  have hf : Summable f := (idealDirichlet_norm_summable _ cubicThetaIdealDensity_norm ht).of_norm
  have hg : Summable g :=
    (idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm cubicThetaRamifiedPrime) ht).of_norm
  rw [cubicThetaInvertedConstantDirichlet_ideal]
  change (∑' ν : CubicThetaUnramifiedIdeal, f ν.val)=(∑' ν, f ν)-(∑' ν, g ν)
  rw [←hf.tsum_sub hg]
  have hsup : Function.support (fun ν => f ν-g ν) ⊆
      {ν | ν cubicThetaRamifiedPrime=0} := by
    intro ν hν
    by_contra hn
    exact hν (by simp [f,g,cubicThetaPrimeDensity,Nat.pos_of_ne_zero hn])
  calc
    _ = ∑' ν : CubicThetaUnramifiedIdeal, (f ν.val-g ν.val) := by
      apply tsum_congr
      intro ν
      simp [g,cubicThetaPrimeDensity,ν.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

def cubicThetaInvertedConstantContinuation (s : ℂ) : ℂ :=
  ((1-(3:ℂ)^(3-3*s))/(1-(3:ℂ)^(2-3*s)))*
    principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)

theorem cubicThetaInvertedConstantContinuation_right {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaInvertedConstantDirichlet s=cubicThetaInvertedConstantContinuation s := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  rw [cubicThetaInvertedConstantDirichlet_difference hs,
    cubicThetaTotientSeries_zeta_quotient ht,cubicThetaRamifiedDensitySeries_eq ht]
  rw [show -(3*s-3)=3-3*s by ring,show (3*s-3)+1=3*s-2 by ring,
    show -(3*s-2)=2-3*s by ring]
  have he : (3:ℂ)^(2-3*s)=(3:ℂ)^(3-3*s)/3 := by
    rw [show 2-3*s=(3-3*s)+(-1:ℂ) by ring,
      Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_neg_one]
    ring
  have hn := cubicTheta_ramified_denominator_ne_zero ht
  rw [show (3*s-3)+1=3*s-2 by ring,show -(3*s-2)=2-3*s by ring] at hn
  unfold cubicThetaInvertedConstantContinuation
  rw [he] at hn ⊢
  have hscalar : (1:ℂ)-(2/3)*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(3-3*s)/3)=
      (1-(3:ℂ)^(3-3*s))/(1-(3:ℂ)^(3-3*s)/3) := by
    apply (eq_div_iff hn).mpr
    rw [sub_mul,one_mul,div_mul_cancel₀ _ hn]
    ring
  calc
    _ = (1-(2/3)*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(3-3*s)/3))*
        (principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)) := by ring
    _ = _ := by rw [hscalar]; ring

end CubicFirstMoment

end

end OAI
