import OAI.NumberTheory.DirichletL.Detector.InitialScales

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma outer_source_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hr : 0<r) :
    W r=verticalIntegral σ (fun w=>(r:ℂ)^(-w)*mellin W w) := by
  simpa only [verticalIntegral,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat] using compactMellin_inversion W a b ha hW (W.smooth (⊤:ℕ∞)) σ r hr

lemma outer_source_scaled_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ N Y : ℝ) (hN : 0<N) (hY : 0<Y) :
    (Y:ℂ)⁻¹*W (N/Y)=
      verticalIntegral σ (fun w=>(Y:ℂ)^(w-1)*(N:ℂ)^(-w)*mellin W w) := by
  rw [outer_source_vertical_inverse W a b ha hW σ (N/Y) (div_pos hN hY)]
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he (w : ℂ) : (Y:ℂ)⁻¹*((N/Y:ℝ):ℂ)^(-w)=(Y:ℂ)^(w-1)*(N:ℂ)^(-w) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hN.le hY.le,div_eq_mul_inv,
      ←Complex.cpow_neg,neg_neg]
    rw [show w-1=(-1)+w by ring,Complex.cpow_add _ _ hy,Complex.cpow_neg_one]
    ring
  unfold verticalIntegral
  simp_rw [←he,mul_assoc,integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
