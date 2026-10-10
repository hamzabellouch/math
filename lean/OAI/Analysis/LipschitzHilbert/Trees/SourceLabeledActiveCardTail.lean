import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledActiveSpectrum

namespace OAI

/-! Only frozen-active labels need slots in the main reference tail.
Their cardinality follows from the original local slope multiplicity,
uniformly over the number of vector coordinates and inactive labels. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem frozenActiveLabels_card_local (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (j : Fin N) {d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M)
    (hK : radius ≤ K)
    (hsupport : ∀ l k, b j l k t ≠ 0 →
      |t-(t+P.rowSlope j l)| ≤ radius*d) :
    (P.frozenActiveLabels t b j).card ≤ (2*K+1)*M := by
  have h := SourceSlopeLabels.active_card_le Finset.univ
    (fun l : P.labels j => t+P.rowSlope j l) (b j) hd hlocal hK
    (fun l _ k hk => hsupport l k hk)
  have hc := Fintype.card_congr (P.frozenActiveLabelsEquiv t b j)
  rw [Fintype.card_coe,Fintype.card_subtype] at hc
  apply hc.trans_le
  convert h using 1
  congr 1
  ext l
  simp only [SourceSlopeLabels.active,Finset.mem_filter,Finset.mem_univ,true_and]

theorem frozenActive_referenceLabels_card_le (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) {B : ℕ}
    (hcard : ∀ j, (P.frozenActiveLabels t b j).card ≤ B)
    (oldSlope newSlope R cone w : ℝ) (j : Fin N) :
    ((P.frozenActiveFamily t b).referenceLabels oldSlope newSlope R cone w j).card ≤ B := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (hcard j)

theorem frozenActiveLabels_card_source (t w Cb : ℝ) (hw : 0 < w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (M K : ℕ) (hK : Cb ≤ K)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) (w/P.length j) M)
    (hsupport : ∀ j l k, b j l k t ≠ 0 →
      |P.rowSlope j l| ≤ Cb*w/P.length j) :
    ∀ j, (P.frozenActiveLabels t b j).card ≤ (2*K+1)*M := by
  intro j
  apply P.frozenActiveLabels_card_local t b j (div_pos hw (P.length_pos j)) (hlocal j) hK
  intro l k hk
  have heq : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  rw [heq,abs_neg]
  simpa only [mul_div_assoc] using hsupport j l k hk

theorem physical_active_narrow_main_square_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (q J F cStar cEta CEta cb Cb : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_narrow_main_square_spectral_tail hVariation B q J F
    cStar cEta CEta cb Cb hq hJ hF hcStar hcEta hCEta hcb hCb hgap] with L htail
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hs : ∀ j l u k xi eta, planarAngularFourier (Q.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact hspectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have ht := htail N κ Label Item Q hP t R w hw hwide hfrequency a ha c hc v hv g hg hg1
    (fun j l k hk => hshort j (P.frozenActiveOriginalLabel t b j l) k hk)
    (P.frozenActive_referenceLabels_card_le t b hcard t t R Cb w) hs
    (fun j l hl => hselector j (P.frozenActiveOriginalLabel t b j l) hl)
    y u H hH hRH
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_frozenActive t b a v g y x
  rw [heq]
  exact ht

theorem physical_active_narrow_centered_masked_variation_spectral_tail
    (hVariation : LepingleInput)
    (B : ℕ) (q J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
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
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_narrow_centered_masked_variation_spectral_tail hVariation B q J A F
    cStar cEta CEta cb Cb maskCone hq hJ hA hF hcStar hcEta hCEta hcb hCb hmaskCone hgap]
    with L htail
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  let altQ := fun j (l : Q.labels j) => alt j (P.frozenActiveOriginalLabel t b j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.frozenActiveOriginalLabel t b j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.frozenActiveOriginalLabel t b j l)
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hs : ∀ j l u k xi eta, planarAngularFourier (Q.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact hspectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have hsAlt : ∀ j l u k xi eta,
      planarAngularFourier ((Q.withProfile altQ hAltQ).physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro j l u k xi eta hx
    exact haltSpectrum j (P.frozenActiveOriginalLabel t b j l) u k xi eta hx
  have hangleQ (j : Fin N) (l : Q.referenceLabels t t R Cb w j) (u : Item j l) :
      |t-(TQ j (Q.referenceOriginalLabel t t R Cb w j l) u).slope| ≤
        maskCone*(TQ j (Q.referenceOriginalLabel t t R Cb w j l) u).width/Q.length j := by
    have hbounds := Q.referenceLabel_bounds t t R Cb w j l
    let pl := P.frozenActiveOriginalLabel t b j (Q.referenceOriginalLabel t t R Cb w j l)
    have hslope : Q.rowSlope j (Q.referenceOriginalLabel t t R Cb w j l) =
        P.rowSlope j pl := rfl
    have hlen : Q.length j = P.length j := rfl
    rw [hslope,hlen] at hbounds
    have hr : |P.rowSlope j pl| ≤ Cb*w/P.length j := by
      simpa only [sub_self,add_zero] using hbounds.2
    exact hangle j pl u hbounds.1 hr
  have ht := htail N κ Label Item Q hP altQ hAltQ t R w hw hwide hfrequency a ha c hc v hv g hg hg1
    (fun j l k hk => hshort j (P.frozenActiveOriginalLabel t b j l) k hk)
    (P.frozenActive_referenceLabels_card_le t b hcard t t R Cb w) hs hsAlt
    (fun j l hl => hselector j (P.frozenActiveOriginalLabel t b j l) hl) TQ
    (fun j l u => hlength j (P.frozenActiveOriginalLabel t b j l) u) hangleQ y u H hH hRH
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_frozenActive t b alt hAlt a v g T L A y x
  rw [heq]
  exact ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
