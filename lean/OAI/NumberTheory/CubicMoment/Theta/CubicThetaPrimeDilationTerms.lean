import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRowEquivalences

namespace OAI

/-! Exact height and summand identities for both primitive branches
of the actual prime-dilated Eisenstein series. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaBottomRow.primeDenominator_height {p : Eisenstein} (hp : primary p)
    (r : CubicThetaBottomRow) (hd : p∣r.d) (z : ℂ × ℝ) :
    r.height (cubicThetaMobius (cubicThetaPrimeDilation (primary_ne_zero hp)) z)=
      ‖(p:ℂ)‖⁻¹*(r.primeDenominator hp hd).height z := by
  have hpC : (p:ℂ)≠0 := fun hz => primary_ne_zero hp (Subtype.ext hz)
  have hn : ‖(p:ℂ)‖^2=norm p := Complex.sq_norm _
  have he : (r.c:ℂ)*((p:ℂ)*z.1)+r.d=(p:ℂ)*((r.c:ℂ)*z.1+(r.d/p:Eisenstein)) := by
    have hdC : (p:ℂ)*(r.d/p:Eisenstein)=r.d := by
      exact_mod_cast EuclideanDomain.mul_div_cancel' (primary_ne_zero hp) hd
    linear_combination -hdC
  have hscalar : ‖(p:ℂ)‖/(‖(p:ℂ)‖^2)=‖(p:ℂ)‖⁻¹ := by
    have hq := norm_ne_zero_iff.mpr hpC
    field_simp
  rw [cubicThetaMobius_primeDilation]
  change (‖(p:ℂ)‖*z.2)/(Complex.normSq ((r.c:ℂ)*((p:ℂ)*z.1)+r.d)+norm r.c*(‖(p:ℂ)‖*z.2)^2)=_
  rw [he,Complex.normSq_mul,mul_pow,hn]
  change (‖(p:ℂ)‖*z.2)/(norm p*Complex.normSq ((r.c:ℂ)*z.1+(r.d/p:Eisenstein))+norm r.c*(norm p*z.2^2))=
    ‖(p:ℂ)‖⁻¹*(z.2/(Complex.normSq ((r.c:ℂ)*z.1+(r.d/p:Eisenstein))+norm r.c*z.2^2))
  rw [show norm p*Complex.normSq ((r.c:ℂ)*z.1+(r.d/p:Eisenstein))+norm r.c*(norm p*z.2^2)=
      norm p*(Complex.normSq ((r.c:ℂ)*z.1+(r.d/p:Eisenstein))+norm r.c*z.2^2) by ring,
    ←hn,←div_mul_div_comm,hscalar]

lemma cubicThetaEisensteinTerm_primeNumerator {p : Eisenstein} (hp : primaryPrime p)
    (r : CubicThetaBottomRow) (hd : ¬p∣r.d) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    cubicThetaEisensteinTerm r (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s=
      star (cubicSymbol p r.d)*(‖(p:ℂ)‖:ℂ)^s*
        cubicThetaEisensteinTerm (r.primeNumerator hp hd) z s := by
  have hunit : star (cubicSymbol p r.d)*cubicSymbol p r.d=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hp.1
      (hp.2.coprime_iff_not_dvd.mpr hd)]
    norm_num
  have hphase : star r.phase=star (cubicSymbol p r.d)*star (r.primeNumerator hp hd).phase := by
    rw [CubicThetaBottomRow.primeNumerator_phase,star_mul,star_star]
    symm
    calc
      _ = (star (cubicSymbol p r.d)*cubicSymbol p r.d)*star r.phase := by ring
      _ = _ := by rw [hunit,one_mul]
  unfold cubicThetaEisensteinTerm
  rw [CubicThetaBottomRow.primeNumerator_height hp r hd z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (_root_.norm_nonneg _) ((r.primeNumerator hp hd).height_pos hz).le,hphase]
  ring

lemma cubicThetaEisensteinTerm_primeDenominator {p : Eisenstein} (hp : primary p)
    (r : CubicThetaBottomRow) (hd : p∣r.d) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    cubicThetaEisensteinTerm r (cubicThetaMobius (cubicThetaPrimeDilation (primary_ne_zero hp)) z) s=
      cubicSymbol p r.c*((‖(p:ℂ)‖⁻¹:ℝ):ℂ)^s*
        cubicThetaEisensteinTerm (r.primeDenominator hp hd) z s := by
  unfold cubicThetaEisensteinTerm
  rw [CubicThetaBottomRow.primeDenominator_height hp r hd z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity : (0:ℝ)≤‖(p:ℂ)‖⁻¹)
      ((r.primeDenominator hp hd).height_pos hz).le,
    CubicThetaBottomRow.primeDenominator_phase hp r hd,star_mul,star_star]
  ring

end CubicFirstMoment

end

end OAI
