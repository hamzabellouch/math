import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! Actual top masks restricted to the affine reference line. The
bandwidth and derivative costs retain the exact top length and slope. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.SlopeBox

def maskLineA (T : SlopeBox) (L A : ℝ) : ℝ := (1/T.length)/L^A
def maskLineB (T : SlopeBox) (L A : ℝ) : ℝ := (-T.x/T.length)/L^A
def maskLineC (T : SlopeBox) (L A t : ℝ) : ℝ := ((t-T.slope)/T.width)/L^A
def maskLineD (T : SlopeBox) (L A y : ℝ) : ℝ := ((y-T.y+T.slope*T.x)/T.width)/L^A

theorem mask_on_reference_line (T : SlopeBox) (L A t y x : ℝ) :
    T.mask L A (x,y+t*x) = sincProductMask ⌈L⌉₊
      (T.maskLineA L A*x+T.maskLineB L A)
      (T.maskLineC L A t*x+T.maskLineD L A y) := by
  unfold mask topSincMask horizontal transverse
  congr 1 <;> dsimp only [maskLineA,maskLineB,maskLineC,maskLineD] <;> ring

theorem mask_on_scaled_reference_line (T : SlopeBox) (L A t y R x : ℝ) :
    T.mask L A (R*x,y+t*(R*x)) = sincProductMask ⌈L⌉₊
      ((R*T.maskLineA L A)*x+T.maskLineB L A)
      ((R*T.maskLineC L A t)*x+T.maskLineD L A y) := by
  rw [T.mask_on_reference_line]
  congr 1 <;> ring

def maskLineBandwidth (T : SlopeBox) (L A t : ℝ) : ℝ :=
  (2*(⌈L⌉₊:ℝ))/(2*Real.pi*L^A)*(1/T.length+|t-T.slope|/T.width)

theorem maskLineBandwidth_eq (T : SlopeBox) (L A t : ℝ) (hL : 0 < L) :
    T.maskLineBandwidth L A t =
      (2*(⌈L⌉₊:ℝ))*((|T.maskLineA L A|+|T.maskLineC L A t|)/(2*Real.pi)) := by
  unfold maskLineBandwidth maskLineA maskLineC
  rw [abs_div,abs_div,abs_div,abs_div,
    abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    abs_of_pos (Real.rpow_pos_of_pos hL A)]
  simp only [abs_one]
  ring

/-- Retained short packets and the actual angular cone give the mask
bandwidth at the packet scale. -/
theorem maskLineBandwidth_packet_le (T : SlopeBox) (L A t ell R : ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hshort : ell ≤ T.length)
    (hcone : |t-T.slope| ≤ R*T.width/ell) :
    T.maskLineBandwidth L A t ≤
      ((2*(⌈L⌉₊:ℝ))/(2*Real.pi*L^A))*((1+R)/ell) := by
  have hx : 1/T.length ≤ 1/ell := one_div_le_one_div_of_le hell hshort
  have hy : |t-T.slope|/T.width ≤ R/ell := by
    apply (div_le_iff₀ T.width_pos).mpr
    convert hcone using 1
    ring
  unfold maskLineBandwidth
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ 1/ell+R/ell := add_le_add hx hy
    _ = (1+R)/ell := by ring

/-- The actual top mask multiplies the original reference-line packet. -/
def referenceMaskedPacket (T : SlopeBox) (L A t y : ℝ)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  sincProductSchwartz f ⌈L⌉₊ (T.maskLineA L A) (T.maskLineB L A)
    (T.maskLineC L A t) (T.maskLineD L A y)

@[simp] theorem referenceMaskedPacket_apply (T : SlopeBox) (L A t y : ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    T.referenceMaskedPacket L A t y f x = (T.mask L A (x,y+t*x):ℂ)*f x := by
  rw [referenceMaskedPacket,sincProductSchwartz_apply,T.mask_on_reference_line]

theorem referenceMaskedPacket_norm_le (T : SlopeBox) (L A t y : ℝ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖T.referenceMaskedPacket L A t y f x‖ ≤ ‖f x‖ :=
  sincProductSchwartz_norm_le f _ _ _ _ _ x

theorem referenceMaskedPacket_deriv_le (T : SlopeBox) (L A t y : ℝ)
    (hL : 0 < L) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖deriv (T.referenceMaskedPacket L A t y f) x‖ ≤
      ‖deriv f x‖+(2*Real.pi*T.maskLineBandwidth L A t)*‖f x‖ := by
  have h := sincProductSchwartz_deriv_le f ⌈L⌉₊ (T.maskLineA L A)
    (T.maskLineB L A) (T.maskLineC L A t) (T.maskLineD L A y) x
  rw [T.maskLineBandwidth_eq L A t hL]
  convert h using 1
  · rfl
  · field_simp [Real.pi_ne_zero]

theorem referenceMaskedPacket_fourier (T : SlopeBox) (L A t y : ℝ)
    (hL : 0 < L) (f : SchwartzMap ℝ ℂ) (lo hi : ℝ)
    (hlow : ∀ xi, |xi| < lo → 𝓕 f xi = 0)
    (hhigh : ∀ xi, hi < |xi| → 𝓕 f xi = 0) :
    (∀ xi, |xi| < lo-T.maskLineBandwidth L A t →
      𝓕 (T.referenceMaskedPacket L A t y f) xi = 0) ∧
    (∀ xi, hi+T.maskLineBandwidth L A t < |xi| →
      𝓕 (T.referenceMaskedPacket L A t y f) xi = 0) := by
  have hl : ∀ xi, |xi| < lo → 𝓕 (f : ℝ → ℂ) xi = 0 := by
    intro xi hxi
    simpa only [SchwartzMap.fourier_coe] using hlow xi hxi
  have hh : ∀ xi, hi < |xi| → 𝓕 (f : ℝ → ℂ) xi = 0 := by
    intro xi hxi
    simpa only [SchwartzMap.fourier_coe] using hhigh xi hxi
  have h := sincProductMask_fourier_annulus f.integrable ⌈L⌉₊
    (T.maskLineA L A) (T.maskLineB L A) (T.maskLineC L A t) (T.maskLineD L A y)
    lo hi hl hh
  rw [← T.maskLineBandwidth_eq L A t hL] at h
  constructor
  · intro xi hxi
    simpa only [SchwartzMap.fourier_coe,referenceMaskedPacket,
      funext (sincProductSchwartz_apply f ⌈L⌉₊ (T.maskLineA L A) (T.maskLineB L A)
        (T.maskLineC L A t) (T.maskLineD L A y))] using h.1 xi hxi
  · intro xi hxi
    simpa only [SchwartzMap.fourier_coe,referenceMaskedPacket,
      funext (sincProductSchwartz_apply f ⌈L⌉₊ (T.maskLineA L A) (T.maskLineB L A)
        (T.maskLineC L A t) (T.maskLineD L A y))] using h.2 xi hxi

end LipschitzHilbert.SlopeBox

end

end OAI
