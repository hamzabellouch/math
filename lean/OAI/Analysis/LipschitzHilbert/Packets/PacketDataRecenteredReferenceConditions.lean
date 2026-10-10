import OAI.Analysis.LipschitzHilbert.Packets.PacketDataActualReferenceEvents
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceWindowBudget

namespace OAI

/-! Original spectra, selectors and assigned packet geometry imply every
local hypothesis of the selected-reference tail theorem after recentering.
The selected packet set may have empty fibers and arbitrary finite support. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem recentered_reference_conditions
    (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (L q oldSlope newSlope referenceLength cone w F Cwide radius Lip cStar cEta CEta cb Cb C : ℝ)
    (E Jcut K Hlabels : ℕ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (horder : 6 ≤ P.order) (hP : P.referenceEnvelopeConstant ≤ L^q)
    (hwindow : Cwide ≤ (2:ℝ)^Jcut) (hwideError : 1 ≤ Cwide*((2:ℝ)^E)^4)
    (hradius : radius ≤ K) (hcutoff : radius+cone ≤ Cwide*((2:ℝ)^E)^4)
    (hE : E = SourceParameters.stepExponent L*SourceParameters.blockCount L)
    (hbandWidth : Cb*w ≤ P.width)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hmotion : ∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j)))
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hlabels)
    (hactive : ∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (haltSpectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (T : τ → SlopeBox) (packets S : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (hS : S ⊆ packets)
    (hlength : ∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1))
    (hwidth : ∀ u ∈ packets, (Cb+C)*w ≤ (T (assigned u)).width) :
    let R := P.recenteredReferenceData alt hAlt oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))
    let selected := P.recenteredReferenceSelection oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency S
    6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = newSlope ∧
    ∃ (c Cwide' radius' : ℝ) (E' Jcut' : ℕ) (w' : ℝ),
      0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide' ≤ c*(2:ℝ)^Jcut' ∧
      1 ≤ Cwide'*((2:ℝ)^E')^4 ∧ radius' ≤ K ∧
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
        (R.angle*(2:ℝ)^j.val) Hlabels) ∧
      (∀ j l k, Measurable (R.selector j l k)) ∧
      (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
      (∀ j l k s, R.selector j l k s ≠ 0 →
        |s-(R.slope+R.family.rowSlope j l)| ≤ radius'*(R.angle*(2:ℝ)^j.val)) ∧
      (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
        ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
          Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
      (∀ j l k s, (Cwide'*((2:ℝ)^E')^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
        R.selector j l k s = 0) ∧
      Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
      Jcut' ≤ Jcut ∧ E' = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
      0 < w' ∧ Cb*w' ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w') ∧
      (∀ j l u k xi eta,
        planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
          |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
            cEta ≤ w'*eta ∧ w'*eta ≤ CEta) ∧
      (∀ j l u k xi eta,
        planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
          R.slope j l u k) (xi,eta) ≠ 0 →
          |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
            cEta ≤ w'*eta ∧ w'*eta ≤ CEta) ∧
      (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
        cb*w'/R.family.length j ≤ |R.family.rowSlope j l| ∧
          |R.family.rowSlope j l| ≤ Cb*w'/R.family.length j) ∧
      (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected →
        R.family.length j ≤ (R.packetTop j l u).length) ∧
      (∀ j (_l : R.family.labels j), R.family.length j ≤ referenceLength) ∧
      (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected →
        R.family.length j ≤ referenceLength →
        |R.family.rowSlope j l| ≤ Cb*w'/R.family.length j →
        |R.slope-(R.packetTop j l u).slope| ≤ 1*(R.packetTop j l u).width/R.family.length j) := by
  intro R selected
  have hmem (j : Fin N) (l : R.family.labels j) (u : Item j l)
      (hu : (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected) :
      (⟨j,⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,u⟩⟩ : P.PacketIndex) ∈ packets :=
    hS (Finset.mem_filter.mp hu).2
  refine ⟨horder,hP,rfl,1,Cwide,radius,E,Jcut,w,div_pos hw P.topLength_pos,
    by norm_num,le_rfl,?_,hwideError,hradius,?_,?_,?_,?_,?_,?_,hv,hf,hf1,
    le_rfl,hE,hw,hbandWidth,hfrequency,?_,?_,?_,?_,?_,?_⟩
  · simpa only [one_mul] using hwindow
  · exact P.reference_normalized_localMultiplicity oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency Hlabels hlocal
  · intro j l k
    exact hb j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) k
  · intro j l k s
    exact hb1 j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) k s
  · exact P.reference_normalized_selector_support oldSlope newSlope referenceLength cone w F radius
      hw hcone hF hwide hfrequency b hsupport
  · intro j l k s _
    exact P.reference_normalized_selector_motion oldSlope newSlope referenceLength cone w F Lip
      hw hcone hF hwide hfrequency b hmotion j l k s
  · exact P.reference_selector_far oldSlope newSlope referenceLength cone w F radius
      (Cwide*((2:ℝ)^E)^4) hw hcone hF hwide hfrequency b hsupport hcutoff
  · exact P.referenceFamily_spectrum oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency cStar cEta CEta hspectrum
  · exact P.reference_alt_spectrum alt hAlt oldSlope newSlope referenceLength cone w F
      cStar cEta CEta hw hcone hF hwide hfrequency haltSpectrum
  · exact P.reference_selector_active_separation oldSlope newSlope referenceLength cone w F
      cb Cb hw hcone hF hwide hfrequency b hactive
  · intro j l u hu
    exact hlength _ (hmem j l u hu)
  · exact P.recenteredReferenceData_short alt hAlt oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))
  · intro j l u hu _ ha
    rw [one_mul]
    exact P.reference_selected_mask_cone T packets assigned oldSlope newSlope referenceLength
      cone w F C Cb hw hcone hF hwide hfrequency hangle hwidth j l u (hmem j l u hu) ha

end LipschitzHilbert.PacketLatticeData

end

end OAI
