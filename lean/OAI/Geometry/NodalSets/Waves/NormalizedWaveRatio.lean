import OAI.Geometry.NodalSets.Elliptic.NormalizedRescaling
import OAI.Geometry.NodalSets.Elliptic.RescaledPhaseDefect

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def planeWave (k : Coord →L[ℝ] ℝ) (s : ℝ) (v : Coord) : ℂ :=
  Complex.exp (Complex.I*(k v/s:ℝ))

lemma planeWave_norm (k : Coord →L[ℝ] ℝ) (s : ℝ) (v : Coord) :
    ‖planeWave k s v‖ = 1 := by
  simp [planeWave,Complex.norm_exp]

lemma normalizedWave_factorization (V amp phi : Coord → ℂ) (S : Coord → ℝ)
    (k : Coord →L[ℝ] ℝ) (N s sigma : ℝ) (x v : Coord)
    (hax : amp x ≠ 0)
    (hx : V x = amp x*Complex.exp ((N:ℂ)*phi x))
    (hz : V (x+(N*s)⁻¹ • v) = amp (x+(N*s)⁻¹ • v)*Complex.exp ((N:ℂ)*phi (x+(N*s)⁻¹ • v))) :
    normalizedRescaling V S N s sigma x v =
      (V x/(sigma:ℂ))*planeWave k s v *
        ((amp (x+(N*s)⁻¹ • v)/amp x)*
          Complex.exp (rescaledPhaseDefect phi (frozenPhaseCovector (fderiv ℝ S x) k) N s x v)) := by
  have hexp : Complex.exp ((N:ℂ)*phi (x+(N*s)⁻¹ • v)) =
      Complex.exp ((N:ℂ)*phi x) * Complex.exp (fderiv ℝ S x v/s:ℝ) * planeWave k s v *
        Complex.exp (rescaledPhaseDefect phi (frozenPhaseCovector (fderiv ℝ S x) k) N s x v) := by
    simp only [planeWave,← Complex.exp_add,rescaledPhaseDefect,frozenPhaseCovector_apply,
      Complex.real_smul,Complex.ofReal_div,Complex.ofReal_inv]
    congr 1
    ring
  rw [normalizedRescaling_eq_div,hz,hx,hexp]
  rw [Complex.ofReal_mul,Complex.ofReal_exp]
  field_simp

lemma ratio_exp_error {a z : ℂ} {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1)
    (ha : ‖a-1‖ ≤ e) (hz : ‖z‖ ≤ e) : ‖a*Complex.exp z-1‖ ≤ 5*e := by
  have hzexp := Complex.norm_exp_sub_one_le (hz.trans he1)
  have hnexp : ‖Complex.exp z‖ ≤ 3 := by
    have h := norm_add_le (Complex.exp z-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at h
    linarith
  have heq : a*Complex.exp z-1 = (a-1)*Complex.exp z+(Complex.exp z-1) := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hprod := mul_le_mul ha hnexp (norm_nonneg _) (by linarith : 0 ≤ e)
  linarith

lemma amplitude_ratio_near_one {a b : ℂ} {e : ℝ} (ha : (1/2:ℝ) ≤ ‖a‖)
    (hb : ‖b-a‖ ≤ e) : ‖b/a-1‖ ≤ 2*e := by
  have hane : a ≠ 0 := by intro h; simp [h] at ha; norm_num at ha
  rw [show b/a-1 = (b-a)/a by field_simp,norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖a‖)).mpr
  have he : 0 ≤ e := (norm_nonneg _).trans hb
  nlinarith

end
end Yau.Geometry

end OAI
