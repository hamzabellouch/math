import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledActiveCardTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodTail

namespace OAI

/-! Original packet spectra and the fixed active-label count discharge
the main-square and masked-variation tails in the physical reference
event. The only remaining component premise is the independently
constructed positive angular-error tail. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_physical_reference_good_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (a q p J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order →
      P.absoluteConstant ≤ L^a → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (c : ℝ), 0 ≤ c →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, P.length j ≤ R → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
          (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_active_narrow_main_square_spectral_tail hVariation B q (J+2) F
      cStar cEta CEta cb Cb hq (by linarith) hF hcStar hcEta hCEta hcb hCb hgap,
    physical_active_narrow_centered_masked_variation_spectral_tail hVariation B q (J+2) A F
      cStar cEta CEta cb Cb maskCone hq (by linarith) hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap,
    eventually_physical_reference_good_tail a q p J] with L hS hV hgood
  intro N κ Label Item _ _ P horder hPa hPq alt hAlt t R w hw hwide hfrequency c hc
    b hb hb1 v hv g hg hg1 hshort hcard hspectrum haltSpectrum hselector T hlength hangle
    y u H hH hRH hE
  have hbFrozen : ∀ j l k, ‖b j l k t‖ ≤ 1 := fun j l k => hb1 j l k t
  have hs := hS N κ Label Item P hPq t R w hw hwide hfrequency c hc b hbFrozen v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  have hvary := hV N κ Label Item P hPq alt hAlt t R w hw hwide hfrequency c hc b hbFrozen
    v hv g hg hg1 hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  have hs' : (volume.restrict (Ico u (u+H)))
      {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ≤
      ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H := by
    apply (measure_mono (show
      {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ⊆
      {x | L^(2*q+9) ≤ |P.physicalMainSquare t c b v g y x|} from ?_)).trans hs.2
    intro x hx
    change L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x at hx
    exact hx.trans (le_abs_self _)
  exact hgood N κ Label Item P horder hPa alt hAlt t c b hb hb1 v hv g hg hg1 T A y u H hH
    hE hs' hvary.2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
