import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledSpectralGoodTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledUniformErrorTail

namespace OAI

/-! Uniform local tails for the actual physical reference bad set.
All three component tails follow from original packet spectra, selector
bounds and slope multiplicity. No tail or active-cardinality premise is
retained, and the threshold is selected before the packet family. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_uniform_physical_reference_good_tail (hVariation : LepingleInput)
    (q J A F cStar cEta CEta cb Cb maskCone Lip : ℝ) (K Hlabels J₀ : ℕ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (_horder : 6 ≤ P.order),
      P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t cutoff c Cwide radius : ℝ) (E Jcut : ℕ)
      (_hcutoff : 0 < cutoff) (_hc : 0 < c) (_hc1 : c ≤ 1)
      (_hC : Cwide ≤ c*(2:ℝ)^Jcut) (_hwideError : 1 ≤ Cwide*((2:ℝ)^E)^4)
      (_hradius : radius ≤ K)
      (_hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (cutoff*(2:ℝ)^j.val) Hlabels)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (_hsupport : ∀ j l k s, b j l k s ≠ 0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(cutoff*(2:ℝ)^j.val))
      (_hnear : ∀ j l k s, |s-t| ≤ c*(cutoff*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(cutoff*(2:ℝ)^j.val)))
      (_hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(cutoff*(2:ℝ)^j.val) < |s-t| →
        b j l k s = 0)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      Jcut ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ (w : ℝ), 0 < w → Cb*w ≤ P.width → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
    ∀ (y u W : ℝ), 0 < W → (∀ j (_l : P.labels j), P.length j ≤ W) →
      (∀ j l u, P.length j ≤ W → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t cutoff b v g T L A
          (q+8) (2*q+9) (2*q+11)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_physical_reference_good_spectral_tail hVariation
      ((2*K+1)*Hlabels) q q (q+1) J A F cStar cEta CEta cb Cb maskCone
      hq hJ hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap,
    eventually_uniform_physicalAngularError_tail q (J+2) 1 Lip hq (by linarith)
      (by norm_num) hLip K Hlabels J₀] with L hgood herror
  intro N κ Label Item _ _ P horder hP alt hAlt t cutoff c Cwide radius E Jcut
    hcutoff hc hc1 hC hwideError hradius hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1
    hJcut hE w hw hwide hfrequency hspectrum haltSpectrum hselector T hlength
    y u W hW hshort hangle
  have hcard (j : Fin N) : (P.frozenActiveLabels t b j).card ≤ (2*K+1)*Hlabels :=
    P.frozenActiveLabels_card_local t b j (mul_pos hcutoff (by positivity)) (hlocal j)
      hradius (fun l k hk => hsupport j l k t hk)
  have he := herror N κ Label Item P horder hP t cutoff c Cwide radius E Jcut
    hcutoff hc hc1 hC hwideError hradius hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1
    hJcut hE y u W hW (fun j l _i => hshort j l)
  have ht := hgood N κ Label Item P horder hP hP alt hAlt t W w hw hwide hfrequency
    cutoff hcutoff.le b hb hb1 v hv g hg hg1 (fun j l _k _hk => hshort j l) hcard
    hspectrum haltSpectrum hselector T hlength hangle y u W hW le_rfl
      (by simpa only [show q+1+7 = q+8 by ring] using he)
  have hexp : max (2*q+10) (q+(q+1)+7)+1 = 2*q+11 := by
    rw [max_eq_left (by linarith)]
    ring
  simpa only [hexp,show q+1+7 = q+8 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
