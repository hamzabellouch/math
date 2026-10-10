import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselIntegral
import Mathlib.Analysis.MellinTransform

namespace OAI

/-! The exact complex Mellin transform of the fixed cubic theta kernel.
Only the order one third needed in the Voronoi construction is used. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBesselHeat_complex_inner {s : ℂ} (hs : 1/6 < s.re)
    {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ)) =
      Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*(t:ℂ)^(s-1/6-1) := by
  have ha : 0 < (s+1/6).re := by norm_num; linarith
  calc
    _ = ((t^(-4/3:ℝ)*Real.exp (-t):ℝ):ℂ)*
        (∫ x in Ioi (0:ℝ), (x:ℂ)^(s+1/6-1)*Complex.exp (-(((1/t:ℝ):ℂ)*(x:ℂ)))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      simp only [cubicBesselHeat,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,
        Complex.ofReal_div,Complex.ofReal_one]
      rw [show -(x:ℂ)/(t:ℂ) = -(1/(t:ℂ)*(x:ℂ)) by ring]
      ring
    _ = ((t^(-4/3:ℝ)*Real.exp (-t):ℝ):ℂ)*
        (((1/(1/t:ℝ):ℝ):ℂ)^(s+1/6)*Complex.Gamma (s+1/6)) := by
      rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha (one_div_pos.mpr ht)]
      simp only [Complex.ofReal_div,Complex.ofReal_one]
    _ = _ := by
      simp only [one_div_one_div,Complex.ofReal_mul]
      rw [Complex.ofReal_cpow ht.le]
      calc
        _ = Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*
            ((t:ℂ)^((-4/3:ℝ):ℂ)*(t:ℂ)^(s+1/6)) := by ring
        _ = _ := by
          rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
          congr 1
          push_cast
          ring_nf

lemma cubicBesselHeat_complex_integrable {s : ℂ} (hs : 1/6 < s.re) :
    Integrable (fun p : ℝ × ℝ => (p.2:ℂ)^(s+1/6-1)*(cubicBesselHeat p.2 p.1:ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hi := cubicBesselHeat_mellin_integrable hs
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.2:ℂ)^(s+1/6-1)*(cubicBesselHeat p.2 p.1:ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply hi.mono' hm
  have ha : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p.1 ∈ Ioi 0 ∧ p.2 ∈ Ioi 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact ⟨ht,hx⟩
  filter_upwards [ha] with p hp
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp.2,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg hp.1)]
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re]
  norm_num

/-- The Gamma product is proved for the literal heat kernel, with its
absolute convergence supplied by the preceding positive-integral estimate. -/
theorem cubicBesselKernel_mellin {s : ℂ} (hs : 1/6 < s.re) :
    mellin (fun x => (cubicBesselKernel x:ℂ)) s =
      Complex.Gamma (s+1/6)*Complex.Gamma (s-1/6) := by
  have hi := cubicBesselHeat_complex_integrable hs
  have hm : 0 < (s-1/6).re := by
    norm_num
    exact hs
  calc
    _ = ∫ x in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ),
        (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul,cubicBesselKernel,Complex.ofReal_mul]
      rw [Complex.ofReal_cpow hx.le,←mul_assoc,
        ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
        show s-1+(1/6:ℝ)=s+1/6-1 by push_cast; ring,
        integral_const_mul,←integral_complex_ofReal]
    _ = ∫ t in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ),
        (x:ℂ)^(s+1/6-1)*(cubicBesselHeat x t:ℂ) := (integral_integral_swap hi).symm
    _ = ∫ t in Ioi (0:ℝ),
        Complex.Gamma (s+1/6)*(Real.exp (-t):ℂ)*(t:ℂ)^(s-1/6-1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicBesselHeat_complex_inner hs ht
    _ = Complex.Gamma (s+1/6)*(∫ t in Ioi (0:ℝ),
        (Real.exp (-t):ℂ)*(t:ℂ)^((s-1/6)-1)) := by
      rw [←integral_const_mul]
      congr 1
      funext t
      ring
    _ = _ := by rw [Complex.Gamma_eq_integral hm]; rfl

end CubicFirstMoment

end

end OAI
