import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGradientMoments
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombTranslation

namespace OAI

/-! The spatial gradient of the actual localized orbital has a finite
24th moment. This supplies the Sobolev cutoff tail for nuclear replacement. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem verticalMode_deriv_moment_integrable {freq : ℝ} (hfreq : 0 < freq) (k : ℕ) :
    Integrable (fun z : ℝ => z^k*deriv (verticalMode freq) z^2) := by
  convert (verticalMode_moment_integrable hfreq (k+2)).const_mul (freq^2) using 1
  funext z
  rw [verticalMode_deriv,pow_add]
  ring

private theorem split_product_moment_integrable (k : ℕ) {f : PlanarPosition → ℝ} {g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf0 : Integrable (fun r => f r^2)) (hfk : Integrable (fun r => ‖r‖^(2*k)*f r^2))
    (hg0 : Integrable (fun z => g z^2)) (hgk : Integrable (fun z => z^(2*k)*g z^2)) :
    Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*(f p.1*g p.2)^2) := by
  have hp := hfk.mul_prod hg0
  have hz := hf0.mul_prod hgk
  apply ((hp.add hz).const_mul ((2:ℝ)^(k-1))).mono'
    ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
      (((hf.comp continuous_fst).mul (hg.comp continuous_snd)).pow 2)).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(‖p.1‖^2+p.2^2)^k*(f p.1*g p.2)^2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
  have h : (‖p.1‖^2+p.2^2)^k ≤ (2:ℝ)^(k-1)*(‖p.1‖^(2*k)+p.2^(2*k)) := by
    simpa only [← pow_mul] using add_pow_le (sq_nonneg ‖p.1‖) (sq_nonneg p.2) k
  convert mul_le_mul_of_nonneg_right h (sq_nonneg (f p.1*g p.2)) using 1
  simp only [mul_pow,Pi.add_apply]
  ring

theorem continuumLocalizedMode_deriv_even_moment_integrable {freq : ℝ} (hfreq : 0 < freq)
    (k : ℕ) (e : Position) :
    Integrable (fun x : Position => ‖x‖^(2*k)*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) := by
  let v := positionSplitCoordinates e
  have hp := split_product_moment_integrable k
    (planarPartial_continuous (normalizedPlanarMode_C7.of_le (by norm_num)) v.1)
    (verticalMode_smooth freq).continuous
    (normalizedPlanarMode_partial_square_integrable v.1)
    (normalizedPlanarMode_partial_moment_integrable v.1 (2*k))
    (verticalMode_square_integrable hfreq) (verticalMode_moment_integrable hfreq (2*k))
  have hz := split_product_moment_integrable k normalizedPlanarMode_C7.continuous
    (((verticalMode_smooth freq).continuous_deriv (by simp)).mul_const v.2)
    normalizedPlanarMode_square_integrable (normalizedPlanarMode_norm_moment_integrable (2*k))
    (by simpa only [mul_pow] using (verticalMode_deriv_square_integrable hfreq).mul_const (v.2^2))
    (by simpa only [mul_pow,mul_assoc] using
      (verticalMode_deriv_moment_integrable hfreq (2*k)).mul_const (v.2^2))
  have hi : Integrable (fun p : SplitPosition => (‖p.1‖^2+p.2^2)^k*
      (fderiv ℝ (localizedMode freq 0) p v)^2) := by
    apply ((hp.add hz).const_mul 2).mono' (by
      exact ((((continuous_fst.norm.pow 2).add (continuous_snd.pow 2)).pow k).mul
        ((((localizedMode_C7 freq 0).continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖(‖p.1‖^2+p.2^2)^k*(fderiv ℝ (localizedMode freq 0) p v)^2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))]
    have h := sq_nonneg (planarPartial normalizedPlanarMode v.1 p.1*verticalMode freq p.2-
      normalizedPlanarMode p.1*(deriv (verticalMode freq) p.2*v.2))
    have hh : (fderiv ℝ (localizedMode freq 0) p v)^2 ≤
        2*((planarPartial normalizedPlanarMode v.1 p.1*verticalMode freq p.2)^2+
          (normalizedPlanarMode p.1*(deriv (verticalMode freq) p.2*v.2))^2) := by
      rw [localizedMode_fderiv,sub_zero]
      nlinarith only [h]
    convert mul_le_mul_of_nonneg_left hh (show 0 ≤ (‖p.1‖^2+p.2^2)^k by positivity) using 1
    simp only [Pi.add_apply]
    ring
  have ht := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hi
  convert ht using 1
  funext x
  simp only [Function.comp_apply,continuumLocalizedMode_fderiv]
  rw [pow_mul,positionSplitCoordinates_norm_sq]

theorem continuumLocalizedMode_deriv_twentyFourth_moment_integrable {freq : ℝ}
    (hfreq : 0 < freq) (e : Position) :
    Integrable (fun x : Position => ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x e)^2) :=
  continuumLocalizedMode_deriv_even_moment_integrable hfreq 12 e

theorem continuumLocalizedMode_deriv_translate (freq : ℝ) (u : PlanarPosition) (x e : Position) :
    fderiv ℝ (continuumLocalizedMode freq u) x e =
      fderiv ℝ (continuumLocalizedMode freq 0) (x-planarCenter u) e := by
  rw [show continuumLocalizedMode freq u =
    (fun y => continuumLocalizedMode freq 0 (y-planarCenter u)) from
      funext (continuumLocalizedMode_translate freq u)]
  rw [fderiv_comp_sub]

end ContinuumCoulomb

end

end OAI
