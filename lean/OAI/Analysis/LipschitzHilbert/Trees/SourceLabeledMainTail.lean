import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMaskedSlots

namespace OAI

/-! Physical main-square and masked-variation tails after exact
recombination of the fixed narrow-label slots. Constants are selected
before the packet family, its scale range, and the physical interval. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalMainSquare (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) : ℝ :=
  Real.sqrt (∑ j, P.physicalMainScale t a b v g j y x^2)

theorem physicalMainSquare_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y : ℝ) :
    Continuous (P.physicalMainSquare t a b v g y) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro j _
  apply Continuous.pow
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  unfold positiveEnvelope lineEnvelope
  apply Continuous.mul continuous_const
  apply Continuous.mul _ continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

theorem physical_main_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ s j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ s j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalMainSquare t a b v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [SourceLatticePacket.physical_centered_square_slot_tail
    hVariation hlo hhi B q J hq hJ] with L htail
  intro N κ Label Item _ _ P hcard hP t a ha b hb v hv g hg hg1 hlow hhigh y u H hH hwidth
  let Q := P.frozenSlot hcard t b hb
  have hconst (s : Fin B) : (Q s).constant ≤ L^q := hP
  have hd (j : Fin N) : 0 ≤ a*(2:ℝ)^j.val := mul_nonneg ha (by positivity)
  have hmono : Monotone (fun j : Fin N => a*(2:ℝ)^j.val) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) ha
  have hwidth' (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) : (Q s).length j ≤ H :=
    hwidth j p.1.1 p.1.2
  obtain ⟨_hm,ht⟩ := htail N κ (fun s => P.SlotItem hcard s) Q hconst
    (fun j => a*(2:ℝ)^j.val) v hv g hg hg1 hd hmono hlow hhigh t t y u H hH hwidth'
  refine ⟨(P.physicalMainSquare_continuous t a b v g y).measurable,?_⟩
  apply (measure_mono (show {x | L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x|} ⊆
    {x | L^(2*q+7) ≤ |∑ s, (Q s).physicalCenteredSquare t t
      (fun j => a*(2:ℝ)^j.val) v g y x|} from ?_)).trans ht
  intro x hx
  have h := P.physicalMainSquare_le_slots hcard t a b hb v g y x
  change L^(2*q+7) ≤ |P.physicalMainSquare t a b v g y x| at hx
  rw [abs_of_nonneg (show 0 ≤ P.physicalMainSquare t a b v g y x from
    Real.sqrt_nonneg _)] at hx
  exact hx.trans (h.trans (le_abs_self _))

theorem physical_centered_masked_variation_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℕ) (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ), 0 ≤ a →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ s j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ s j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenSlot hcard t b hb s).raw 0 j u k y) xi = 0) →
      (∀ j l u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
      (∀ j l u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j l u k y) xi = 0) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, |t-(T j l u).slope| ≤ cone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ H) →
      Measurable (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [SourceLatticePacket.physical_centered_masked_variation_slot_tail
    hVariation hlo hhi B q J A cone hq hJ hA hcone] with L htail
  intro N κ Label Item _ _ P hcard hP alt hAlt t a ha b hb v hv g hg hg1
    hlow hhigh hSlow hShigh T hshort hangle y u H hH hwidth
  let Q := P.slotted hcard
  have hconst (s : Fin B) : (Q s).constant ≤ L^q := hP
  have hd (j : Fin N) : 0 ≤ a*(2:ℝ)^j.val := mul_nonneg ha (by positivity)
  have hmono : Monotone (fun j : Fin N => a*(2:ℝ)^j.val) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) ha
  have hslow (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) (k : κ) (y xi : ℝ)
      (hxi : |xi| < (lo/(Q s).topLength)*(2:ℝ)^j.val) :
      𝓕 (((Q s).withProfile (P.slottedAlt hcard alt s)
        (P.slottedAlt_bound hcard alt hAlt s)).raw 0 j p k y) xi = 0 := by
    rw [P.slotted_alt_raw hcard alt hAlt]
    exact hSlow j p.1.1 p.1.2 k y xi hxi
  have hshigh (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) (k : κ) (y xi : ℝ)
      (hxi : (hi/(Q s).topLength)*(2:ℝ)^j.val < |xi|) :
      𝓕 (((Q s).withProfile (P.slottedAlt hcard alt s)
        (P.slottedAlt_bound hcard alt hAlt s)).raw 0 j p k y) xi = 0 := by
    rw [P.slotted_alt_raw hcard alt hAlt]
    exact hShigh j p.1.1 p.1.2 k y xi hxi
  obtain ⟨_hm,ht⟩ := htail N κ (fun s => P.SlotItem hcard s) Q hconst
    (fun s j p k => b j p.1.1 k t) (fun s j p k => hb j p.1.1 k)
    (P.slottedAlt hcard alt) (P.slottedAlt_bound hcard alt hAlt)
    (fun j => a*(2:ℝ)^j.val) v hv g hg hg1 hd hmono hlow hhigh hslow hshigh
    (fun s j p => T j p.1.1 p.1.2) t
    (fun s j p => hshort j p.1.1 p.1.2) (fun s j p => hangle j p.1.1 p.1.2)
    y u H hH (fun s j p => hwidth j p.1.1 p.1.2)
  refine ⟨(P.physicalCenteredMaskedVariation_continuous alt hAlt t a b v g T L A y).measurable,?_⟩
  apply (measure_mono (show
    {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x|} ⊆
    {x | L^(2*q+8) ≤ |∑ s, (Q s).physicalCenteredMaskedVariation
      (fun j p k => b j p.1.1 k t) (P.slottedAlt hcard alt s)
      (P.slottedAlt_bound hcard alt hAlt s) (fun j => a*(2:ℝ)^j.val) v g
      (fun j p => T j p.1.1 p.1.2) L A t y x|} from ?_)).trans ht
  intro x hx
  have h := P.physicalCenteredMaskedVariation_le_slots alt hAlt t a b v g T L A y hcard hb x
  change L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x| at hx
  rw [abs_of_nonneg (show 0 ≤ P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x from
    cubicVariation_nonneg _ _)] at hx
  exact hx.trans (h.trans (le_abs_self _))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
