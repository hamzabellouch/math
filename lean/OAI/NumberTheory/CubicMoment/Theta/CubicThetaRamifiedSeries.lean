import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedIdeal

namespace OAI

/-! The exact ramified local factor of the normalized totient series. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedDensitySeries (s : ℂ) : ℂ :=
  normDirichletSeries (cubicThetaPrimeDensity cubicThetaRamifiedPrime) idealExponentNorm s

lemma cubicTheta_ramified_denominator_ne_zero {s : ℂ} (hs : 1<s.re) :
    1-(3:ℂ)^(-(s+1))≠0 := by
  have hn : ‖(3:ℂ)^(-(s+1))‖<1 := by
    change ‖((3:ℝ):ℂ)^(-(s+1))‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re,Complex.add_re,Complex.one_re]
    linarith
  intro he
  have hpow := (sub_eq_zero.mp he).symm
  rw [hpow,norm_one] at hn
  exact lt_irrefl 1 hn

theorem cubicThetaRamifiedDensitySeries_eq {s : ℂ} (hs : 1<s.re) :
    cubicThetaRamifiedDensitySeries s=
      ((2/3:ℂ)*(3:ℂ)^(-s)/(1-(3:ℂ)^(-(s+1))))*
        (principalIdealZeta s/principalIdealZeta (s+1)) := by
  have he := cubicThetaPrimeDensity_series_equation cubicThetaRamifiedPrime hs
  rw [cubicThetaRamifiedPrime_norm] at he
  change cubicThetaRamifiedDensitySeries s=(3:ℂ)^(-s)*
    ((1-(3:ℂ)⁻¹)*normDirichletSeries cubicThetaIdealDensity idealExponentNorm s+
      (3:ℂ)⁻¹*cubicThetaRamifiedDensitySeries s) at he
  have hshift : (3:ℂ)^(-(s+1))=(3:ℂ)^(-s)/3 := by
    rw [show -(s+1)=-s+(-1) by ring,Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),
      Complex.cpow_neg_one,div_eq_mul_inv]
  have hb : cubicThetaRamifiedDensitySeries s*(1-(3:ℂ)^(-(s+1)))=
      (2/3:ℂ)*(3:ℂ)^(-s)*normDirichletSeries cubicThetaIdealDensity idealExponentNorm s := by
    rw [hshift]
    linear_combination he
  calc
    _ = ((2/3:ℂ)*(3:ℂ)^(-s)*
        normDirichletSeries cubicThetaIdealDensity idealExponentNorm s)/
        (1-(3:ℂ)^(-(s+1))) := (eq_div_iff (cubicTheta_ramified_denominator_ne_zero hs)).mpr hb
    _ = _ := by rw [cubicThetaTotientSeries_zeta_quotient hs]; ring

end CubicFirstMoment

end

end OAI
