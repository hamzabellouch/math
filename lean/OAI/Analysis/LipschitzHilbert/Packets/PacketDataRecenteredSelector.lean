import OAI.Analysis.LipschitzHilbert.Packets.PacketDataParentReference

namespace OAI

/-! The selector mesh and physical centers survive exact recentering.
Only selected items enter the packet-top and mask-cone conclusions. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_angular_mesh (w : ℝ) (j : Fin N) :
    (w/P.topLength)*(2:ℝ)^j.val = w/P.length j := by
  unfold length
  field_simp

theorem reference_normalized_localMultiplicity
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w) (M : ℕ)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) M) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : Q.labels j => newSlope+Q.rowSlope j l)
      ((w/P.topLength)*(2:ℝ)^j.val) M := by
  intro Q j
  rw [P.reference_angular_mesh w j]
  exact P.referenceFamily_localMultiplicity oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j (w/P.length j) M (hlocal j)

theorem reference_normalized_selector_support
    (oldSlope newSlope R cone w F radius : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j)) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, b j (orig j l) k s ≠ 0 →
      |s-(newSlope+Q.rowSlope j l)| ≤ radius*((w/P.topLength)*(2:ℝ)^j.val) := by
  intro Q orig j l k s hs
  rw [P.reference_angular_mesh w j]
  exact P.referenceFamily_selector_support oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency b (fun _ => radius) (fun j => w/P.length j)
    hsupport j l k s hs

theorem reference_normalized_selector_motion
    (oldSlope newSlope R cone w F Lip : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hmotion : ∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, ‖b j (orig j l) k s-b j (orig j l) k newSlope‖ ≤
      Lip*(|s-newSlope|/((w/P.topLength)*(2:ℝ)^j.val)) := by
  intro Q orig j l k s
  rw [P.reference_angular_mesh w j]
  exact hmotion j (orig j l) k s newSlope

theorem reference_alt_spectrum
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (oldSlope newSlope R cone w F cStar cEta CEta : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) u k xi eta,
      planarAngularFourier ((Q.withProfile (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l))).physicalPacket newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro Q orig j l u k xi eta hxi
  exact (P.withProfile alt hAlt).referenceFamily_spectrum oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency cStar cEta CEta hspectrum j l u k xi eta hxi

theorem reference_selector_far
    (oldSlope newSlope R cone w F radius cutoff : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hcutoff : radius+cone ≤ cutoff) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, cutoff*((w/P.topLength)*(2:ℝ)^j.val) < |s-newSlope| →
      b j (orig j l) k s = 0 := by
  intro Q orig j l k s hs
  by_contra hn
  have hb := hsupport j (orig j l) k s hn
  have hl := (P.referenceLabel_bounds oldSlope newSlope R cone w j l).2
  have hdist : |(oldSlope+P.rowSlope j (orig j l))-newSlope| ≤ cone*(w/P.length j) := by
    calc
      _ = |P.rowSlope j (orig j l)+(oldSlope-newSlope)| := by congr 1; ring
      _ ≤ cone*w/P.length j := hl
      _ = _ := by ring
  have ht := abs_sub_le s (oldSlope+P.rowSlope j (orig j l)) newSlope
  rw [P.reference_angular_mesh w j] at hs
  have hm := mul_le_mul_of_nonneg_right hcutoff (div_pos hw (P.length_pos j)).le
  have hle : |s-newSlope| ≤ cutoff*(w/P.length j) := by
    calc
      _ ≤ _ := ht
      _ ≤ radius*(w/P.length j)+cone*(w/P.length j) := add_le_add hb hdist
      _ = (radius+cone)*(w/P.length j) := by ring
      _ ≤ _ := hm
  exact (not_lt_of_ge hle) hs

theorem reference_selector_active_separation
    (oldSlope newSlope R cone w F cb Cb : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hactive : ∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j), (∃ k, b j (orig j l) k newSlope ≠ 0) →
      cb*w/Q.length j ≤ |Q.rowSlope j l| ∧ |Q.rowSlope j l| ≤ Cb*w/Q.length j := by
  intro Q orig j l hl
  obtain ⟨k,hk⟩ := hl
  have h := hactive j (orig j l) k newSlope hk
  have heq : newSlope-(oldSlope+P.rowSlope j (orig j l)) =
      -(P.rowSlope j (orig j l)+(oldSlope-newSlope)) := by ring
  simpa only [Q,referenceFamily,heq,abs_neg,length,SourceLabeledLattice.length] using h

theorem reference_selected_mask_cone
    {τ : Type*} (T : τ → SlopeBox) (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ)
    (oldSlope newSlope R cone w F C Cb : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1))
    (hwidth : ∀ u ∈ packets, (Cb+C)*w ≤ (T (assigned u)).width)
    (j : Fin N)
    (l : (P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).labels j)
    (u : Item j l)
    (hmem : (⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩ : P.PacketIndex) ∈ packets)
    (hactive : |(P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).rowSlope j l| ≤
      Cb*w/P.length j) :
    |newSlope-(T (assigned ⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩)).slope| ≤
      (T (assigned ⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩)).width/P.length j := by
  let orig := P.referenceOriginalLabel oldSlope newSlope R cone w j l
  have ha := hangle ⟨j,⟨orig,u⟩⟩ hmem
  have hw' := hwidth ⟨j,⟨orig,u⟩⟩ hmem
  have heq : newSlope-(oldSlope+P.rowSlope j orig) =
      -(P.rowSlope j orig+(oldSlope-newSlope)) := by ring
  have hb : |newSlope-(oldSlope+P.rowSlope j orig)| ≤ Cb*w/P.length j := by
    simpa only [heq,abs_neg,referenceFamily] using hactive
  have ht := abs_sub_le newSlope (oldSlope+P.rowSlope j orig)
    (T (assigned ⟨j,⟨orig,u⟩⟩)).slope
  have hm := div_le_div_of_nonneg_right hw' (P.length_pos j).le
  change |newSlope-(T (assigned ⟨j,⟨orig,u⟩⟩)).slope| ≤ _
  calc
    _ ≤ _ := ht
    _ ≤ Cb*w/P.length j+C*(w/P.length j) := add_le_add hb ha
    _ = (Cb+C)*w/P.length j := by ring
    _ ≤ _ := hm

end LipschitzHilbert.PacketLatticeData

end

end OAI
