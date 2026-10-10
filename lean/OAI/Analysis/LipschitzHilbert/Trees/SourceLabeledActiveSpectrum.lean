import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledNarrowTail

namespace OAI

/-! The active narrow reference annuli follow from the original
two-dimensional packet spectrum. The selector's lower angular separation
is used only on labels that occur in the frozen main sum. All three
covariant jets inherit these annuli, including alternate synthesis
profiles on the same physical geometry. -/

noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_fourier_cutoffs_at (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ)
    (hspectrum : ∀ xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : cb*w/P.length j ≤ |P.rowSlope j l| ∧
      |P.rowSlope j l| ≤ Cb*w/P.length j)
    (i : Fin 3) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 (P.raw i j l u k y) xi = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j l)| ∧
      |t-(t+P.rowSlope j l)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
    simpa only [heq,abs_neg] using hselector
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j l u k)
    y t (t+P.rowSlope j l) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb hspectrum hsel (P.frequency k) P.scale i
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← P.raw_eq_physical_slice i j l u k y t,heq,heq] at h
  exact h

variable (t R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel t t R cone w

theorem referenceSelf_active_raw_cutoffs (cStar cEta CEta cb Cb : ℝ)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j l, (∃ k, b j l k t ≠ 0) →
      cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : (Q).labels j) (hactive : ∃ k, b j (orig j l) k t ≠ 0)
    (u : Item j l) (k : κ) (i : Fin 3) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val →
      𝓕 ((Q).raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 ((Q).raw i j l u k y) xi = 0) := by
  have hs := P.referenceFamily_spectrum t t R cone w F hw hcone hF hwide hfrequency
    cStar cEta CEta hspectrum j l u k
  have hsel : cb*w/(Q).length j ≤ |(Q).rowSlope j l| ∧
      |(Q).rowSlope j l| ≤ Cb*w/(Q).length j := by
    simpa only [referenceFamily,sub_self,add_zero,length] using hselector j (orig j l) hactive
  exact (Q).raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
    j l u k hs hsel i y

theorem referenceSelf_active_alt_raw_cutoffs
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j l, (∃ k, b j l k t ≠ 0) →
      cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : (Q).labels j) (hactive : ∃ k, b j (orig j l) k t ≠ 0)
    (u : Item j l) (k : κ) (i : Fin 3) (y : ℝ) :
    let altQ := fun j (l : (Q).labels j) => alt j (orig j l)
    let hAltQ := fun j (l : (Q).labels j) => hAlt j (orig j l)
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val →
      𝓕 (((Q).withProfile altQ hAltQ).raw i j l u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/(Q).topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 (((Q).withProfile altQ hAltQ).raw i j l u k y) xi = 0) := by
  exact (P.withProfile alt hAlt).referenceSelf_active_raw_cutoffs
    t R cone w F hw hcone hF hwide hfrequency cStar cEta CEta cb Cb hcEta hcb hCb
    b hspectrum hselector j l hactive u k i y

theorem physical_narrow_main_square_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (q J F cStar cEta CEta cb Cb : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.referenceLabels t t R Cb w j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  have hlo : 0 < (cEta*cb-cStar)/(2*Real.pi) :=
    div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) Real.pi_pos)
  have hhi : 0 ≤ (CEta*Cb+cStar)/(2*Real.pi) :=
    div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  filter_upwards [physical_narrow_main_square_tail hVariation hlo hhi B q J F Cb hq hJ hF hCb]
    with L htail
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum hselector y u H hH hRH
  have hsupport : ∀ j l k, b j l k t ≠ 0 →
      |t+P.rowSlope j l-t| ≤ Cb*w/P.length j := by
    intro j l k hk
    have heq : t+P.rowSlope j l-t = P.rowSlope j l := by ring
    rw [heq]
    exact (hselector j l ⟨k,hk⟩).2
  apply htail N κ Label Item P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport hcard
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).2 xi hxi
  · exact hH
  · exact hRH

theorem physical_narrow_centered_masked_variation_spectral_tail (hVariation : LepingleInput)
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
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.referenceLabels t t R Cb w j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j (l : P.referenceLabels t t R Cb w j) u,
        |t-(T j (P.referenceOriginalLabel t t R Cb w j l) u).slope| ≤
          maskCone*(T j (P.referenceOriginalLabel t t R Cb w j l) u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  have hlo : 0 < (cEta*cb-cStar)/(2*Real.pi) :=
    div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) Real.pi_pos)
  have hhi : 0 ≤ (CEta*Cb+cStar)/(2*Real.pi) :=
    div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  filter_upwards [physical_narrow_centered_masked_variation_tail hVariation hlo hhi
    B q J A F Cb maskCone hq hJ hA hF hCb hmaskCone] with L htail
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hcard hspectrum haltSpectrum hselector T hlength hangle y u H hH hRH
  have hsupport : ∀ j l k, b j l k t ≠ 0 →
      |t+P.rowSlope j l-t| ≤ Cb*w/P.length j := by
    intro j l k hk
    have heq : t+P.rowSlope j l-t = P.rowSlope j l := by ring
    rw [heq]
    exact (hselector j l ⟨k,hk⟩).2
  apply htail N κ Label Item P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport hcard
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta cb Cb hcEta hcb hCb b hspectrum hselector j l hl u k 0 y).2 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_alt_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      alt hAlt cStar cEta CEta cb Cb hcEta hcb hCb b haltSpectrum hselector j l hl u k 0 y).1 xi hxi
  · intro j l hl u k y xi hxi
    exact (P.referenceSelf_active_alt_raw_cutoffs t R Cb w F hw hCb hF hwide hfrequency
      alt hAlt cStar cEta CEta cb Cb hcEta hcb hCb b haltSpectrum hselector j l hl u k 0 y).2 xi hxi
  · exact hlength
  · exact hangle
  · exact hH
  · exact hRH

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
