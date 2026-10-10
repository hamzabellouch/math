import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction
import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals

namespace OAI

/-! Removing labels with no items preserves every packet and every
source band. Only genuinely populated assigned fibers enter label counts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def inhabitedLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => Nonempty (Item j l))

def inhabitedOriginalLabel (j : Fin N) (l : P.inhabitedLabels j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

theorem inhabitedLabel_nonempty (j : Fin N) (l : P.inhabitedLabels j) : Nonempty (Item j l) :=
  (Finset.mem_filter.mp l.property).2

def inhabitedFamily : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.inhabitedLabels
  originX := fun j l => P.originX j (P.inhabitedOriginalLabel j l)
  originZ := fun j l => P.originZ j (P.inhabitedOriginalLabel j l)
  rowSlope := fun j l => P.rowSlope j (P.inhabitedOriginalLabel j l)
  frequency := P.frequency
  site := fun j l => P.site j (P.inhabitedOriginalLabel j l)
  site_injective := fun j l => P.site_injective j (P.inhabitedOriginalLabel j l)
  profile := fun j l => P.profile j (P.inhabitedOriginalLabel j l)
  profile_bound := fun j l => P.profile_bound j (P.inhabitedOriginalLabel j l)
  shear_bound := fun j l => P.shear_bound j (P.inhabitedOriginalLabel j l)
  carrier_bound := fun j l => P.carrier_bound j (P.inhabitedOriginalLabel j l)

@[simp] theorem inhabitedFamily_length (j : Fin N) : P.inhabitedFamily.length j = P.length j := rfl
@[simp] theorem inhabitedFamily_actualX (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) :
    P.inhabitedFamily.actualX j l u = P.actualX j (P.inhabitedOriginalLabel j l) u := rfl
@[simp] theorem inhabitedFamily_actualZ (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) :
    P.inhabitedFamily.actualZ j l u = P.actualZ j (P.inhabitedOriginalLabel j l) u := rfl
@[simp] theorem inhabitedFamily_rowSlope (j : Fin N) (l : P.inhabitedLabels j) :
    P.inhabitedFamily.rowSlope j l = P.rowSlope j (P.inhabitedOriginalLabel j l) := rfl
@[simp] theorem inhabitedFamily_constant : P.inhabitedFamily.constant = P.constant := rfl
@[simp] theorem inhabitedFamily_absoluteConstant : P.inhabitedFamily.absoluteConstant = P.absoluteConstant := rfl
@[simp] theorem inhabitedFamily_label_card (j : Fin N) :
    (P.inhabitedFamily.labels j).card = ((P.labels j).filter (fun l => Nonempty (Item j l))).card := rfl

def inhabitedItemsEquiv (j : Fin N) :
    (Σ l : P.inhabitedLabels j, Item j l) ≃ Σ l : P.labels j, Item j l where
  toFun := fun p => ⟨P.inhabitedOriginalLabel j p.1,p.2⟩
  invFun := fun p => ⟨⟨p.1.val,Finset.mem_filter.mpr ⟨p.1.property,⟨p.2⟩⟩⟩,p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem sum_inhabited {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ l : P.inhabitedLabels j, ∑ u : Item j l, f (P.inhabitedOriginalLabel j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.inhabitedItemsEquiv j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ l : P.inhabitedLabels j, Item j l, f (P.inhabitedOriginalLabel j p.1) p.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

@[simp] theorem inhabitedFamily_raw (jet : Fin 3) (j : Fin N)
    (l : P.inhabitedLabels j) (u : Item j l) (k : κ) (y : ℝ) :
    P.inhabitedFamily.raw jet j l u k y = P.raw jet j (P.inhabitedOriginalLabel j l) u k y := rfl

@[simp] theorem inhabitedFamily_physicalPacket (t : ℝ) (j : Fin N)
    (l : P.inhabitedLabels j) (u : Item j l) (k : κ) :
    P.inhabitedFamily.physicalPacket t j l u k =
      P.physicalPacket t j (P.inhabitedOriginalLabel j l) u k := rfl

theorem inhabitedFamily_physicalMultiplierCoefficient (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) :
    P.inhabitedFamily.physicalMultiplierCoefficient t
      (fun j l => b j (P.inhabitedOriginalLabel j l)) v f j l u =
      P.physicalMultiplierCoefficient t b v f j (P.inhabitedOriginalLabel j l) u := rfl

theorem inhabitedFamily_rawBand
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.inhabitedFamily.rawBand (fun j l u => coeff j (P.inhabitedOriginalLabel j l) u) jet j x y =
      P.rawBand coeff jet j x y := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,Fintype.sum_sigma]
  exact P.sum_inhabited j (fun l u => coeff j l u k*P.raw jet j l u k y x)

theorem inhabitedFamily_rawInterval
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.inhabitedFamily.rawInterval (fun j l u => coeff j (P.inhabitedOriginalLabel j l) u)
      jet lower upper x y = P.rawInterval coeff jet lower upper x y := by
  rw [rawInterval_eq_band_sum _ _ _ _ _ hlu,rawInterval_eq_band_sum _ _ _ _ _ hlu]
  simp_rw [P.inhabitedFamily_rawBand]

theorem inhabitedLabels_card_le (j : Fin N) (S : Finset (Label j))
    (hS : ∀ l : P.labels j, Nonempty (Item j l) → l.val ∈ S) :
    (P.inhabitedLabels j).card ≤ S.card := by
  apply Finset.card_le_card
  intro l hl
  obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hl
  exact hS ⟨l,hm⟩ hn

def inhabitedAlternate (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j (P.inhabitedOriginalLabel j l) u k

theorem inhabitedAlternate_bound
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) (k : κ) :
    planarProfileConstant (P.inhabitedAlternate alt j l u k) (2*P.inhabitedFamily.order) ≤
      P.inhabitedFamily.profileBound := hAlt j (P.inhabitedOriginalLabel j l) u k

theorem inhabitedFamily_withProfile
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound) :
    (P.withProfile alt hAlt).inhabitedFamily =
      P.inhabitedFamily.withProfile (P.inhabitedAlternate alt) (P.inhabitedAlternate_bound alt hAlt) := rfl

theorem inhabitedFamily_physicalMaskedBand
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
    (L A y : ℝ) (j : Fin N) (x : ℝ) :
    P.inhabitedFamily.physicalMaskedBand (P.inhabitedAlternate alt) (P.inhabitedAlternate_bound alt hAlt)
      t (fun j l => b j (P.inhabitedOriginalLabel j l)) v f
      (fun j l u => T j (P.inhabitedOriginalLabel j l) u) L A y j x =
      P.physicalMaskedBand alt hAlt t b v f T L A y j x := by
  ext k
  simp only [physicalMaskedBand,WithLp.ofLp_toLp]
  change (∑ l : P.inhabitedLabels j, ∑ u : Item j l,
    P.physicalMultiplierCoefficient t b v f j (P.inhabitedOriginalLabel j l) u k *
      ((T j (P.inhabitedOriginalLabel j l) u).mask L A (x,y+t*x):ℂ) *
      (P.withProfile alt hAlt).physicalPacket t j (P.inhabitedOriginalLabel j l) u k (x,y+t*x)) = _
  exact P.sum_inhabited j (fun l u => P.physicalMultiplierCoefficient t b v f j l u k *
    ((T j l u).mask L A (x,y+t*x):ℂ) * (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
