import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLatticeData
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationSpectral
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedConcentrationWeighted

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem source_frozen_spectral_jet_neighborhood_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d → ∀ (T : SlopeBox) (K w : ℝ) (D : ℕ), 0 < K → 0 < w →
      (∀ j u k xi eta, planarAngularFourier (P.physicalPacket T.slope j u k) (xi,eta) ≠ 0 →
        |xi+(T.slope+P.rowSlope j)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket T.slope j u k)
            (xi,eta) ≠ 0 →
        |xi+(T.slope+P.rowSlope j)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j| ∧
        |P.rowSlope j| ≤ Cb*w/P.length j) →
      SourceSupportedLatticeTopGeometry P T K D → ∀ (i : Fin 2) (J L : ℝ),
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z shift, |shift| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
            (fun j u k y x => (P.withProfile alt hAlt).raw (i.castLE (by decide)) j u k y x)
            a b z.1 ((z.2-T.slope*z.1)+shift)‖ ≤
              (P.family.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  let lo := (cEta*cb-cStar)/(2*Real.pi)
  let hi := (CEta*Cb+cStar)/(2*Real.pi)
  have hlo : 0 < lo := div_pos (sub_pos.mpr hgap) (by positivity)
  have hhi : 0 ≤ hi := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨Ab,Am,hAb,hAm,hgood⟩ := frozen_jet_top_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd T K w D hK hw hspectrum haltSpectrum hselector G i J L
  let S : SourceLatticeSpectralData (P.withProfile alt hAlt) := {
    referenceSlope := T.slope
    w := w
    cStar := cStar
    cEta := cEta
    CEta := CEta
    cb := cb
    Cb := Cb
    w_pos := hw
    cEta_pos := hcEta
    cb_nonneg := hcb
    Cb_nonneg := hCb
    spectrum := haltSpectrum
    selector := hselector }
  have hlow j u k y xi hxi : 𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0 :=
    (P.frozenProfile_fourier_cutoffs c hc T.slope w cStar cEta CEta cb Cb hw hcEta hcb hCb
      hspectrum (fun j u _ _ => hselector j u) 0 j u k y).1 xi hxi
  have hhigh j u k y xi hxi : 𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0 :=
    (P.frozenProfile_fourier_cutoffs c hc T.slope w cStar cEta CEta cb Cb hw hcEta hcb hCb
      hspectrum (fun j u _ _ => hselector j u) 0 j u k y).2 xi hxi
  have Galt : SourceSupportedLatticeTopGeometry (P.withProfile alt hAlt) T K D := {
    length_le := G.length_le
    width_le := G.width_le
    centerX_le := G.centerX_le
    centerZ_le := G.centerZ_le
    order_le := G.order_le
    scale_eq := G.scale_eq }
  exact hgood N κ ι P c hc alt hAlt d v hv g hg hg1 hd hlow hhigh T K D hK
    ((P.withProfile alt hAlt).supportedTopRawData S T K D Galt)
    ((P.withProfile alt hAlt).supportedTopCovariantData S T K D Galt) i J L

end LipschitzHilbert.SourceLatticePacket

end

end OAI
