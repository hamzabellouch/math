import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarPlancherel

namespace OAI

/-! Actual nonzero Gram interactions force the angular proximity used
in the selected-tree Bessel argument. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

private theorem common_wedge_distance (xi eta theta phi ell r w cStar cEta : ℝ)
    (hell : 0<ell) (hr : 0<r) (hw : 0<w) (hcEta : 0<cEta)
    (he : cEta≤w*eta) (hs : |xi+theta*eta|≤cStar/ell)
    (ht : |xi+phi*eta|≤cStar/r) :
    |theta-phi|≤(cStar/cEta)*(w/ell+w/r) := by
  have heta : 0<eta := by nlinarith
  have hdiff : |(theta-phi)*eta|≤cStar/ell+cStar/r := by
    calc
      _ = |(xi+theta*eta)-(xi+phi*eta)| := by congr 1; ring
      _ ≤ |xi+theta*eta|+|xi+phi*eta| := abs_sub _ _
      _ ≤ _ := add_le_add hs ht
  have hscaled : |theta-phi| * cEta≤w*(cStar/ell+cStar/r) := by
    calc
      _ ≤ |theta-phi| * (w*eta) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = w*|(theta-phi)*eta| := by rw [abs_mul,abs_of_pos heta]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hw.le
  have h := (le_div_iff₀ hcEta).mpr hscaled
  convert h using 1
  field_simp

theorem planar_packet_gram_angle (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta phi ell r w cStar cEta CEta : ℝ)
    (hell : 0<ell) (hr : 0<r) (hw : 0<w) (hcEta : 0<cEta)
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hg : ∀ xi eta, planarAngularFourier g (xi,eta)≠0 →
      |xi+phi*eta|≤cStar/r ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    |theta-phi|≤(cStar/cEta)*(w/ell+w/r) := by
  obtain ⟨xi,eta,hfi,hgi⟩ := exists_common_angular_frequency f g hinner
  exact common_wedge_distance xi eta theta phi ell r w cStar cEta hell hr hw hcEta
    (hf xi eta hfi).2.1 (hf xi eta hfi).1 (hg xi eta hgi).1

/-- A sufficiently longer interacting packet lies close to the longer
tree's direction in units of the shorter packet's angular scale. -/
theorem gram_short_direction (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (theta phi t ell r w cStar cEta CEta cOne COmega CZero : ℝ)
    (hell : 0<ell) (hr : 0<r) (hw : 0<w) (hcStar : 0≤cStar)
    (hcEta : 0<cEta) (hCOmega : 0≤COmega) (hCZero : 0<CZero)
    (hlong : CZero*ell≤r)
    (hconstants : (cStar/cEta)*(1+1/CZero)+COmega/CZero≤cOne/4)
    (htop : |phi-t|≤COmega*(w/r))
    (hf : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hg : ∀ xi eta, planarAngularFourier g (xi,eta)≠0 →
      |xi+phi*eta|≤cStar/r ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (hinner : (∫ z, inner ℂ (f z) (g z) ∂volume.prod volume)≠0) :
    |theta-t|≤(cOne/4)*(w/ell) := by
  have hgram := planar_packet_gram_angle f g theta phi ell r w cStar cEta CEta
    hell hr hw hcEta hf hg hinner
  have hscale : w/r≤(1/CZero)*(w/ell) := by
    apply (div_le_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_left hlong (div_nonneg hw.le (mul_pos hCZero hell).le)
    convert h using 1 <;> field_simp
  have hc : 0≤cStar/cEta := div_nonneg hcStar hcEta.le
  calc
    _ ≤ |theta-phi|+|phi-t| := abs_sub_le _ _ _
    _ ≤ (cStar/cEta)*(w/ell+w/r)+COmega*(w/r) := add_le_add hgram htop
    _ ≤ (cStar/cEta)*(w/ell+(1/CZero)*(w/ell))+COmega*((1/CZero)*(w/ell)) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hscale) hc)
        (mul_le_mul_of_nonneg_left hscale hCOmega)
    _ = ((cStar/cEta)*(1+1/CZero)+COmega/CZero)*(w/ell) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconstants (div_nonneg hw.le hell.le)

/-- The near-extremal direction rule rules out the wrong temporal order
once these two geometric slope estimates hold. -/
theorem selected_direction_order_contradiction
    (theta t selected other d cOne epsilon : ℝ)
    (hd : 0<d) (hcOne : 0<cOne)
    (hnear : |theta-t|≤cOne*d/4)
    (hselected : theta+cOne*d≤selected)
    (hother : |other-t|≤cOne*d/4)
    (hepsilon : epsilon≤cOne*d/4)
    (hfirst : selected<other+epsilon) : False := by
  have h1 := (abs_le.mp hnear).1
  have h2 := (abs_le.mp hother).2
  have hpos : 0<cOne*d := mul_pos hcOne hd
  nlinarith

end LipschitzHilbert

end

end OAI
