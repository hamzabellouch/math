import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcedCusp

namespace OAI

/-! The incoming cutoff vanishes at the inverted high cusp. The actual
inverted Eisenstein series is consequently square integrable on that strip. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInvertedRow_height_le_one (r : CubicThetaInvertedRow)
    {p : ℂ × ℝ} (hp : 1<p.2) : r.height p≤1 := by
  have hn := one_le_norm (primary_ne_zero r.c_primary)
  have hd : 0<Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
    nlinarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d),sq_nonneg (p.2-1)]
  change p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)≤1
  apply (div_le_one hd).mpr
  nlinarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d),sq_nonneg (p.2-1)]

theorem cubicThetaIncomingEisenstein_inverted_zero {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=0 := by
  have hz : ∀ r : CubicThetaBottomRow, cubicThetaIncomingTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=0 := by
    intro r
    unfold cubicThetaIncomingTerm
    rw [cubicThetaBottomRow_height_inverted r (by linarith),
      cubicThetaCuspCutoff_zero (cubicThetaInvertedRow_height_le_one _ hp),zero_mul]
  simp only [cubicThetaIncomingEisenstein,hz,tsum_zero]

lemma cubicThetaArithmeticRemainder_inverted {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s := by
  rw [cubicThetaArithmeticRemainder,cubicThetaIncomingEisenstein_inverted_zero hp,sub_zero]

lemma cubicThetaSection_strip_memLp (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (fun p : CubicThetaPoint => F.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mpr
  have hn : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.integrable_norm_pow (by norm_num)
  have hi := hn.integrableOn (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)
  unfold IntegrableOn at hi
  rw [←cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))] at hi
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using
    hi.comp_measurable cubicThetaQuotientMap_open.continuous.measurable

lemma cubicThetaInvertedEisenstein_strip_memLp {s : ℂ} (hs : 3<s.re) :
    MemLp (fun p : CubicThetaPoint => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have h := cubicThetaSection_strip_memLp
    (cubicThetaInversionSection (cubicThetaArithmeticSection s (by linarith)))
    (cubicThetaInversionSection_memLp _ (cubicThetaArithmeticSection_memLp hs))
  apply h.ae_eq
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  change cubicThetaArithmeticRemainder
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s=_
  exact cubicThetaArithmeticRemainder_inverted (by have h:=hp.1; change 2<p.val.2 at h; linarith) s

end CubicFirstMoment

end

end OAI
