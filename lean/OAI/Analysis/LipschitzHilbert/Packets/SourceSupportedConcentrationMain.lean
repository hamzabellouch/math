import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLabeledGeometry
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationMain
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedConcentrationMainSlots
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationActive

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem source_selector_main_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb) (J a p : ℝ) (D B : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ)
      (T : τ → SlopeBox),
      (∀ top j l k, ‖b top j l k (T top).slope‖ ≤ 1) →
      (∀ top j, ((P top).frozenActiveLabels (T top).slope (b top) j).card ≤ B) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (angle : τ → ℝ), (∀ top, 0 ≤ angle top) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (w : ℝ), 0 < w →
      (∀ top k, |(P top).frequency k| ≤ F/w) →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, (∃ k, b top j l k (T top).slope ≠ 0) →
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let V := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
              (b top) (v top) (g top)) 0 lower upper x y
          ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => V z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+7)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,hLt,_hBt,hconc⟩ := source_labeled_centered_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap J a (p+1) D B
    hJ ha (by linarith)
  refine ⟨max Lt (F*Cb+2),hLt.trans (le_max_left _ _),?_⟩
  intro L hLL τ κ _ _ N Label Item _ P hP b T hb hcard alt hAlt angle hangle
    v hv g hg hg1 w hw hfreq hspectrum haltSpectrum hselector G
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hLL)
  have hCL : F*Cb+2 ≤ L := (le_max_right _ _).trans hLL
  let Q := fun top => (P top).activeMainFamily (T top).slope (b top) w F Cb hw hF hCb
    (hfreq top) (fun j l hl => (hselector top j l hl).2)
  let orig := fun top j => (P top).frozenActiveOriginalLabel (T top).slope (b top) j
  let altQ := fun top j l => alt top j (orig top j l)
  let hAltQ := fun top j l => hAlt top j (orig top j l)
  let bQ := fun top j l k (_s : ℝ) => b top j (orig top j l) k (T top).slope
  have hQ (top : τ) : (Q top).constant ≤ L^(p+1) := by
    rw [(P top).activeMainFamily_constant]
    calc
      _ ≤ L^p*L := mul_le_mul (hP top) hCL (by positivity) (Real.rpow_nonneg hLpos.le _)
      _ = _ := by rw [Real.rpow_add hLpos p 1,Real.rpow_one]
  have hs : ∀ top j l u k xi eta,
      planarAngularFourier ((Q top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
      |xi+((T top).slope+(Q top).rowSlope j l)*eta| ≤ cStar/(Q top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro top j l u k xi eta hx
    exact hspectrum top j (orig top j l) u k xi eta hx
  have hsAlt : ∀ top j l u k xi eta,
      planarAngularFourier (((Q top).withProfile (altQ top) (hAltQ top)).physicalPacket
        (T top).slope j l u k) (xi,eta) ≠ 0 →
      |xi+((T top).slope+(Q top).rowSlope j l)*eta| ≤ cStar/(Q top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro top j l u k xi eta hx
    exact haltSpectrum top j (orig top j l) u k xi eta hx
  have hsel : ∀ top j (l : (Q top).labels j) (_u : Item top j l),
      cb*w/(Q top).length j ≤ |(Q top).rowSlope j l| ∧
        |(Q top).rowSlope j l| ≤ Cb*w/(Q top).length j := by
    intro top j l _u
    exact hselector top j (orig top j l)
      ((P top).frozenActiveLabel_nonzero (T top).slope (b top) j l)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc L ((le_max_left _ _).trans hLL)
    τ κ N Label Item Q hcard hQ bQ (fun top j l k => hb top j (orig top j l) k)
    altQ hAltQ angle hangle v hv g hg hg1 T w hw hs hsAlt hsel
    (fun top => (P top).activeMainFamily_supportedTopGeometry (T top).slope (b top) w F Cb hw hF hCb
      (hfreq top) (fun j l hl => (hselector top j l hl).2) (G top))
  refine ⟨bad,hbad,harea,?_⟩
  intro top lower upper hlu hu z shift hshift hout
  have h := hpoint top lower upper hlu hu z shift hshift hout
  let V := fun x y => ((Q top).withProfile (altQ top) (hAltQ top)).rawInterval
    ((Q top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
      (fun j l k _ => bQ top j l k 0) (v top) (g top)) 0 lower upper x y
  have heq (x y : ℝ) : V x y = ((P top).withProfile (alt top) (hAlt top)).rawInterval
      ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
        (b top) (v top) (g top)) 0 lower upper x y := by
    exact (P top).activeMainFamily_rawInterval (T top).slope (b top) w F Cb hw hF hCb
      (hfreq top) (fun j l hl => (hselector top j l hl).2)
      (alt top) (hAlt top) (angle top) (v top) (g top) 0 lower upper hlu x y
  have heqfun (x : ℝ) : V x = fun y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
      ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
        (b top) (v top) (g top)) 0 lower upper x y := funext (heq x)
  change ‖V z.1 _‖+(T top).width*‖covariantSignal (P top).frequency
    (fun k y => V z.1 y k) _‖ ≤ _ at h
  rw [heqfun] at h
  simpa only [show 2*(p+1)+5 = 2*p+7 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
