import OAI.Analysis.LipschitzHilbert.Trees.SourceGramGeometry

namespace OAI

/-! The fixed angular margin of an actual packet transfers to every
direction sufficiently close to its slope, using a common Fourier witness. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

private theorem frequency_slope_distance (xi eta theta ell w cStar cEta : ℝ)
    (hell : 0<ell) (hw : 0<w) (hcEta : 0<cEta)
    (he : cEta≤w*eta) (hs : |xi+theta*eta|≤cStar/ell) :
    |theta-(-xi/eta)|≤(cStar/cEta)*(w/ell) := by
  have heta : 0<eta := by nlinarith
  have hid : |theta-(-xi/eta)| * eta=|xi+theta*eta| := by
    calc
      _ = |(theta-(-xi/eta))*eta| := by rw [abs_mul,abs_of_pos heta]
      _ = _ := by congr 1; field_simp; ring
  have hbound : |theta-(-xi/eta)| * cEta≤w*(cStar/ell) := by
    calc
      _ ≤ |theta-(-xi/eta)| * (w*eta) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = w*|xi+theta*eta| := by rw [←hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hw.le
  have h := (le_div_iff₀ hcEta).mpr hbound
  convert h using 1
  field_simp

/-- This uses the manuscript's support margin, not an assumed angular
membership for the direction that will be used in deletion. -/
theorem gram_margin_direction_mem (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta ell w cStar cEta margin u : ℝ) (omega : Set ℝ)
    (hell : 0<ell) (hw : 0<w) (hcEta : 0<cEta)
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta|≤cStar/ell ∧ cEta≤w*eta)
    (hmargin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      Icc (-xi/eta-margin*(w/ell)) (-xi/eta+margin*(w/ell))⊆omega)
    (hu : |u-theta|≤(margin-cStar/cEta)*(w/ell))
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) : u∈omega := by
  obtain ⟨xi,eta,hfi,_⟩ := exists_common_angular_frequency f g hinner
  have hd := frequency_slope_distance xi eta theta ell w cStar cEta hell hw hcEta
    (hf xi eta hfi).2 (hf xi eta hfi).1
  have hu' : |u-(-xi/eta)|≤margin*(w/ell) := by
    calc
      _ ≤ |u-theta|+|theta-(-xi/eta)| := abs_sub_le _ _ _
      _ ≤ (margin-cStar/cEta)*(w/ell)+(cStar/cEta)*(w/ell) := add_le_add hu hd
      _ = _ := by ring
  apply hmargin xi eta hfi
  obtain ⟨hl,hr⟩ := abs_le.mp hu'
  constructor <;> linarith

end LipschitzHilbert

end

end OAI
