import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledActiveReference

namespace OAI

/-! Main reference tails use only the fixed narrow cone and the labels
whose frozen selector is nonzero. Thus the wide error-cone carrier bound
never enters the constants, and inactive synthesis profiles need no
annular hypothesis. -/

noncomputable section
open Filter MeasureTheory Set FourierTransform
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem frozenSlot_fourier_eq (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (s : Fin B) (i : Fin 3) (j : Fin N) (u : P.SlotItem hcard s j)
    (k : κ) (y xi : ℝ) :
    𝓕 ((P.frozenSlot hcard t b hb s).raw i j u k y) xi =
      b j u.1.1 k t • 𝓕 (P.raw i j u.1.1 u.1.2 k y) xi := by
  unfold frozenSlot
  rw [SourceLatticePacket.frozenProfile_raw, P.slotted_raw hcard,
    fourier_smul, smul_apply]

theorem physical_main_square_active_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j l u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_main_square_tail hVariation hlo hhi B q J hq hJ] with L htail
  intro N κ Label Item _ _ P hcard hP t a ha b hb v hv g hg hg1 hlow hhigh y u H hH hwidth
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hcardQ (j : Fin N) : (Q.labels j).card ≤ B :=
    (P.frozenActiveLabels_card_le t b j).trans (hcard j)
  have hlowQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hlow j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hhighQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hhigh j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  obtain ⟨hm,ht⟩ := htail N κ Label Item Q hcardQ hP t a ha c hc v hv g hg hg1
    hlowQ hhighQ y u H hH (fun j l i => hwidth j (P.frozenActiveOriginalLabel t b j l) i)
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_frozenActive t b a v g y x
  rw [heq]
  exact ⟨hm,ht⟩

theorem physical_centered_masked_variation_active_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
          𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
      (∀ j l, (∃ k, b j l k t ≠ 0) → ∀ u k y xi,
        (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
          𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, |t-(T j l u).slope| ≤ cone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_tail
    hVariation hlo hhi B q J A cone hq hJ hA hcone] with L htail
  intro N κ Label Item _ _ P hcard hP alt hAlt t a ha b hb v hv g hg hg1
    hlow hhigh hslow hshigh T hshort hangle y u H hH hwidth
  let Q := P.frozenActiveFamily t b
  let c := P.frozenActiveSelector t b
  let altQ := fun j (l : Q.labels j) => alt j (P.frozenActiveOriginalLabel t b j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.frozenActiveOriginalLabel t b j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.frozenActiveOriginalLabel t b j l)
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.frozenActiveOriginalLabel t b j l) k
  have hcardQ (j : Fin N) : (Q.labels j).card ≤ B :=
    (P.frozenActiveLabels_card_le t b j).trans (hcard j)
  have hlowQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hlow j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hhighQ (s : Fin B) (j : Fin N) (p : Q.SlotItem hcardQ s j)
      (k : κ) (y xi : ℝ) (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.frozenSlot hcardQ t c hc s).raw 0 j p k y) xi = 0 := by
    rw [Q.frozenSlot_fourier_eq hcardQ t c hc,
      P.frozenActiveFamily_raw t b]
    rw [hhigh j _ (P.frozenActiveLabel_nonzero t b j p.1.1) p.1.2 k y xi hxi, smul_zero]
  have hslowQ (j : Fin N) (l : Q.labels j) (u : Item j l) (k : κ) (y xi : ℝ)
      (hxi : |xi| < (lo/Q.topLength)*(2:ℝ)^j.val) :
      𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0 := by
    rw [P.frozenActiveFamily_alt_raw t b alt hAlt]
    exact hslow j _ (P.frozenActiveLabel_nonzero t b j l) u k y xi hxi
  have hshighQ (j : Fin N) (l : Q.labels j) (u : Item j l) (k : κ) (y xi : ℝ)
      (hxi : (hi/Q.topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0 := by
    rw [P.frozenActiveFamily_alt_raw t b alt hAlt]
    exact hshigh j _ (P.frozenActiveLabel_nonzero t b j l) u k y xi hxi
  obtain ⟨hm,ht⟩ := htail N κ Label Item Q hcardQ hP altQ hAltQ t a ha c hc v hv g hg hg1
    hlowQ hhighQ hslowQ hshighQ TQ
    (fun j l u => hshort j (P.frozenActiveOriginalLabel t b j l) u)
    (fun j l u => hangle j (P.frozenActiveOriginalLabel t b j l) u)
    y u H hH (fun j l i => hwidth j (P.frozenActiveOriginalLabel t b j l) i)
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_frozenActive t b alt hAlt a v g T L A y x
  rw [heq]
  exact ⟨hm,ht⟩

theorem physical_narrow_main_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J F cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (t R w : ℝ) (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) →
    let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
    let c := fun j (l : Q.labels j) k s =>
      b j (P.referenceOriginalLabel t t R cone w j l) k s
    (∀ j, (Q.labels j).card ≤ B) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+9) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_main_square_active_tail hVariation hlo hhi B (q+1) J
    (by linarith) hJ, eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (F*cone+2)] with L htail hL hFC
  intro N κ Label Item _ _ P hP t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport
  dsimp only
  intro hcard hlow hhigh y u H hH hRH
  let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
  let c := fun j (l : Q.labels j) k s =>
    b j (P.referenceOriginalLabel t t R cone w j l) k s
  have hconst : Q.constant ≤ L^(q+1) := by
    rw [P.referenceSelf_constant t R cone w F hw hcone hF hwide hfrequency]
    calc
      P.absoluteConstant*(F*cone+2) ≤ L^q*L :=
        mul_le_mul hP hFC (by positivity) (Real.rpow_nonneg (by linarith) q)
      _ = L^(q+1) := by rw [Real.rpow_add (by linarith : 0 < L),Real.rpow_one]
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.referenceOriginalLabel t t R cone w j l) k
  have hwidth (j : Fin N) (l : Q.labels j) (_i : Item j l) : Q.length j ≤ H :=
    (P.referenceLabel_bounds t t R cone w j l).1.trans hRH
  have ht := htail N κ Label Item Q hcard hconst t a ha c hc v hv g hg hg1
    hlow hhigh y u H hH hwidth
  have heq : P.physicalMainSquare t a b v g y = Q.physicalMainSquare t a c v g y := by
    funext x
    exact P.physicalMainSquare_eq_narrow_reference t R cone w F hw hcone hF hwide hfrequency
      a b v g hshort hsupport y x
  rw [heq]
  simpa only [show 2*(q+1)+7 = 2*q+9 by ring] using ht

theorem physical_narrow_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A F cone maskCone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hmaskCone : 0 ≤ maskCone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (_hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) →
    let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
    let c := fun j (l : Q.labels j) k s =>
      b j (P.referenceOriginalLabel t t R cone w j l) k s
    let altQ := fun j (l : Q.labels j) => alt j (P.referenceOriginalLabel t t R cone w j l)
    let hAltQ := fun j (l : Q.labels j) => hAlt j (P.referenceOriginalLabel t t R cone w j l)
    (∀ j, (Q.labels j).card ≤ B) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (Q.raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      |xi| < (lo/Q.topLength)*(2:ℝ)^j.val →
        𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0) →
    (∀ j l, (∃ k, c j l k t ≠ 0) → ∀ u k y xi,
      (hi/Q.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((Q.withProfile altQ hAltQ).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j (l : Q.labels j) u, |t-(T j (P.referenceOriginalLabel t t R cone w j l) u).slope| ≤
        maskCone*(T j (P.referenceOriginalLabel t t R cone w j l) u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_centered_masked_variation_active_tail
    hVariation hlo hhi B (q+1) J A maskCone (by linarith) hJ hA hmaskCone,
    eventually_ge_atTop (1:ℝ), eventually_ge_atTop (F*cone+2)] with L htail hL hFC
  intro N κ Label Item _ _ P hP alt hAlt t R w hw hwide hfrequency a ha b hb v hv g hg hg1
    hshort hsupport
  dsimp only
  intro hcard hlow hhigh hslow hshigh T hlength hangle y u H hH hRH
  let Q := P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
  let c := fun j (l : Q.labels j) k s =>
    b j (P.referenceOriginalLabel t t R cone w j l) k s
  let altQ := fun j (l : Q.labels j) => alt j (P.referenceOriginalLabel t t R cone w j l)
  have hAltQ : ∀ j l u k, planarProfileConstant (altQ j l u k) (2*Q.order) ≤ Q.profileBound :=
    fun j l u k => hAlt j (P.referenceOriginalLabel t t R cone w j l) u k
  let TQ := fun j (l : Q.labels j) => T j (P.referenceOriginalLabel t t R cone w j l)
  have hconst : Q.constant ≤ L^(q+1) := by
    rw [P.referenceSelf_constant t R cone w F hw hcone hF hwide hfrequency]
    calc
      P.absoluteConstant*(F*cone+2) ≤ L^q*L :=
        mul_le_mul hP hFC (by positivity) (Real.rpow_nonneg (by linarith) q)
      _ = L^(q+1) := by rw [Real.rpow_add (by linarith : 0 < L),Real.rpow_one]
  have hc : ∀ j l k, ‖c j l k t‖ ≤ 1 := fun j l k =>
    hb j (P.referenceOriginalLabel t t R cone w j l) k
  have hwidth (j : Fin N) (l : Q.labels j) (_i : Item j l) : Q.length j ≤ H :=
    (P.referenceLabel_bounds t t R cone w j l).1.trans hRH
  have ht := htail N κ Label Item Q hcard hconst altQ hAltQ t a ha c hc v hv g hg hg1
    hlow hhigh hslow hshigh TQ
    (fun j l i => hlength j (P.referenceOriginalLabel t t R cone w j l) i)
    hangle y u H hH hwidth
  have heq : P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y =
      Q.physicalCenteredMaskedVariation altQ hAltQ t a c v g TQ L A y := by
    funext x
    exact P.physicalCenteredMaskedVariation_eq_narrow_reference
      t R cone w F hw hcone hF hwide hfrequency alt hAlt a b v g T L A y x hshort hsupport
  rw [heq]
  simpa only [show 2*(q+1)+8 = 2*q+10 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
