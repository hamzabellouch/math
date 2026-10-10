import OAI.Analysis.IntegralMeans.DomainArea
import OAI.Analysis.IntegralMeans.KoebeReduction

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_inverse_areaMoment (s : ℝ) :
    areaMoment koebeInverse koebeDomain s = areaMoment koebeMap disk (2 - s) := by
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  have hopen : IsOpen disk := Metric.isOpen_ball
  unfold areaMoment koebeDomain
  rw [conformal_lintegral_eq (F := koebeMap) (s := disk) hdisk
    (fun z hz => (koebeMap_hasDerivAt hz).differentiableAt)
    koebeMap_schlicht.1.2]
  apply setLIntegral_congr_fun hdisk
  intro z hz
  change ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 : ℕ)) *
    ENNReal.ofReal (‖deriv koebeInverse (koebeMap z)‖ ^ s) =
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 - s))
  have hderiv : deriv koebeInverse (koebeMap z) = (deriv koebeMap z)⁻¹ :=
    (univalent_inverse_hasDerivAt hopen koebeMap_schlicht.1 hz).deriv
  rw [hderiv, norm_inv, Real.inv_rpow (norm_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have hn : 0 < ‖deriv koebeMap z‖ :=
    norm_pos_iff.mpr (univalent_deriv_ne_zero hopen koebeMap_schlicht.1 hz)
  rw [← Real.rpow_natCast ‖deriv koebeMap z‖ 2,
    ← Real.rpow_neg hn.le, ← Real.rpow_add hn]
  rfl

lemma not_integrable_of_areaMoment_top {f : ℂ → ℂ} {U : Set ℂ} {t : ℝ}
    (h : areaMoment f U t = ⊤) :
    ¬ IntegrableOn (fun z => ‖deriv f z‖ ^ t) U volume := by
  intro hi
  have hf := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (norm_nonneg (deriv f z)) t))).mp hi.hasFiniteIntegral
  change areaMoment f U t < ⊤ at hf
  rw [h] at hf
  exact lt_irrefl _ hf

end Brennan.Sharp

end

end OAI
