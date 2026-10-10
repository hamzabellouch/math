import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilationTerms

namespace OAI

/-! A literal two-branch expansion of the prime-dilated Eisenstein
series. The identities use the actual primitive-row bijections. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeUpperRows (p : Eisenstein) (z : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : {r : CubicThetaBottomRow // p∣r.c},
    star (cubicSymbol p r.val.d)*cubicThetaEisensteinTerm r.val z s

def cubicThetaPrimeLowerRows (p : Eisenstein) (z : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : {r : CubicThetaBottomRow // ¬p∣r.c},
    cubicSymbol p r.val.c*cubicThetaEisensteinTerm r.val z s

lemma cubicThetaPrimeDilation_numerator_sum {p : Eisenstein} (hp : primaryPrime p)
    {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    (∑' r : {r : CubicThetaBottomRow // ¬p∣r.d},
      cubicThetaEisensteinTerm r.val (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s)=
      (‖(p:ℂ)‖:ℂ)^s*cubicThetaPrimeUpperRows p z s := by
  rw [cubicThetaPrimeUpperRows,←(cubicThetaPrimeNumeratorRowEquiv hp).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro r
  rw [cubicThetaEisensteinTerm_primeNumerator hp r.val r.property hz]
  change star (cubicSymbol p r.val.d)*(‖(p:ℂ)‖:ℂ)^s*
    cubicThetaEisensteinTerm (r.val.primeNumerator hp r.property) z s=
      (‖(p:ℂ)‖:ℂ)^s*(star (cubicSymbol p r.val.d)*
        cubicThetaEisensteinTerm (r.val.primeNumerator hp r.property) z s)
  ring

lemma cubicThetaPrimeDilation_denominator_sum {p : Eisenstein} (hp : primaryPrime p)
    {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    (∑' r : {r : CubicThetaBottomRow // p∣r.d},
      cubicThetaEisensteinTerm r.val (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s)=
      ((‖(p:ℂ)‖⁻¹:ℝ):ℂ)^s*cubicThetaPrimeLowerRows p z s := by
  rw [cubicThetaPrimeLowerRows,←(cubicThetaPrimeDenominatorRowEquiv hp).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro r
  rw [cubicThetaEisensteinTerm_primeDenominator hp.1 r.val r.property hz]
  change cubicSymbol p r.val.c*((‖(p:ℂ)‖⁻¹:ℝ):ℂ)^s*
    cubicThetaEisensteinTerm (r.val.primeDenominator hp.1 r.property) z s=
      ((‖(p:ℂ)‖⁻¹:ℝ):ℂ)^s*(cubicSymbol p r.val.c*
        cubicThetaEisensteinTerm (r.val.primeDenominator hp.1 r.property) z s)
  ring

theorem cubicThetaEisenstein_primeDilation_unfold {p : Eisenstein} (hp : primaryPrime p)
    {z : ℂ × ℝ} (hz : 0<z.2) {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s=
      (‖(p:ℂ)‖:ℂ)^s*cubicThetaPrimeUpperRows p z s+
      ((‖(p:ℂ)‖⁻¹:ℝ):ℂ)^s*cubicThetaPrimeLowerRows p z s := by
  have hsum := cubicThetaEisenstein_summable
    (cubicThetaMobius_height_pos (cubicThetaPrimeDilation hp.2.ne_zero) hz) hs
  have he := hsum.tsum_subtype_add_tsum_subtype_compl {r : CubicThetaBottomRow | p∣r.d}
  change (∑' r : {r : CubicThetaBottomRow // p∣r.d},
      cubicThetaEisensteinTerm r.val (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s)+
    (∑' r : {r : CubicThetaBottomRow // ¬p∣r.d},
      cubicThetaEisensteinTerm r.val (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s)=_ at he
  rw [cubicThetaPrimeDilation_denominator_sum hp hz,cubicThetaPrimeDilation_numerator_sum hp hz] at he
  exact he.symm.trans (add_comm _ _)

end CubicFirstMoment

end

end OAI
