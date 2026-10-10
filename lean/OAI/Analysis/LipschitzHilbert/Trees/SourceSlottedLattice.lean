import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

/-- Common packet bounds with a finite set of translated lattice labels
at each scale. All bounds are imposed only on labels that are present. -/
structure SourceLabeledLattice (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  carrierBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
  carrierBound_nonneg : 0 ≤ carrierBound
  labels : ∀ j, Finset (Label j)
  originX : ∀ j, labels j → ℝ
  originZ : ∀ j, labels j → ℝ
  rowSlope : ∀ j, labels j → ℝ
  frequency : κ → ℝ
  site : ∀ j (l : labels j), Item j l → ℤ × ℤ
  site_injective : ∀ j l, Function.Injective (site j l)
  profile : ∀ j (l : labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ
  profile_bound : ∀ j l u k,
    planarProfileConstant (profile j l u k) (2 * order) ≤ profileBound
  shear_bound : ∀ j l, |rowSlope j l * (topLength / (2 : ℝ) ^ j.val) / width| ≤ 1
  carrier_bound : ∀ j l k,
    |frequency k * rowSlope j l * (topLength / (2 : ℝ) ^ j.val)| ≤ carrierBound

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originX j l + P.length j * (P.site j l u).1

def actualZ (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originZ j l + P.rowSlope j l * P.length j * (P.site j l u).1 +
    P.width * (P.site j l u).2

def raw (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ)
    (y : ℝ) : SchwartzMap ℝ ℂ :=
  modulatedPlanarJet (P.profile j l u k) (P.actualX j l u) (P.actualZ j l u)
    (P.length j) P.width (-P.rowSlope j l) (P.frequency k) P.scale y (P.length_pos j).ne' i

def physicalPacket (t : ℝ) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  physicalPlanarPacket (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u + t * P.actualX j l u) (P.length j) P.width
    (t + P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

def constant : ℝ :=
  ((2 ^ P.order * P.profileBound) * (P.carrierBound + 2) * P.ratioBound ^ 2) *
    3 ^ (2 * P.order)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

def slotEmbedding (j : Fin N) : P.labels j ↪ Fin B := SourceSlopeLabels.slots P.labels hcard j

abbrev SlotItem (b : Fin B) (j : Fin N) :=
  SourceSlopeLabels.SlotItem (P.slotEmbedding hcard j) (fun l => Item j l) b

instance slotItemFintype (b : Fin B) (j : Fin N) : Fintype (P.SlotItem hcard b j) := by
  unfold SlotItem SourceSlopeLabels.SlotItem
  infer_instance

/-- Every original item occurs in exactly one slot. -/
def slotItemsEquiv (j : Fin N) :
    (Σ b : Fin B, P.SlotItem hcard b j) ≃ Σ l : P.labels j, Item j l where
  toFun p := p.2.1
  invFun p := ⟨P.slotEmbedding hcard j p.1, ⟨p, rfl⟩⟩
  left_inv := by
    rintro ⟨b, ⟨p, hp⟩⟩
    cases hp
    rfl
  right_inv := fun _ => rfl

/-- Splitting by slots is an exact identity for arbitrary finite packet
sums, not an estimate and not a change to the waves. -/
theorem sum_slotted {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ b : Fin B, ∑ p : P.SlotItem hcard b j, f p.1.1 p.1.2) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.slotItemsEquiv hcard j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ b : Fin B, P.SlotItem hcard b j, f p.2.1.1 p.2.1.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

/-- The value is used only when the corresponding slot has an item.
Zero is a harmless geometric default when that slot is empty. -/
def slotValue (b : Fin B) (j : Fin N) (f : P.labels j → ℝ) : ℝ :=
  (SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b).elim 0 f

theorem slotValue_item (b : Fin B) (j : Fin N) (f : P.labels j → ℝ)
    (p : P.SlotItem hcard b j) : P.slotValue hcard b j f = f p.1.1 := by
  unfold slotValue
  rw [SourceSlopeLabels.slotItem_label (P.slotEmbedding hcard j) p]
  rfl

/-- One genuine translated-lattice family per slot. No hypotheses on a
selector are introduced for missing labels or empty scales. -/
def slotted (b : Fin B) : SourceLatticePacket N κ (P.SlotItem hcard b) where
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
  originX := fun j => P.slotValue hcard b j (P.originX j)
  originZ := fun j => P.slotValue hcard b j (P.originZ j)
  rowSlope := fun j => P.slotValue hcard b j (P.rowSlope j)
  frequency := P.frequency
  site := fun j p => P.site j p.1.1 p.1.2
  site_injective := fun j => SourceSlopeLabels.slotItem_site_injective
    (P.slotEmbedding hcard j) (P.site j) (P.site_injective j) b
  profile := fun j p k => P.profile j p.1.1 p.1.2 k
  profile_bound := fun j p k => P.profile_bound j p.1.1 p.1.2 k
  shear_bound := by
    intro j
    cases h : SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b with
    | none => simp [slotValue, h]
    | some l => simpa [slotValue, h] using P.shear_bound j l
  carrier_bound := by
    intro j k
    cases h : SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b with
    | none => simpa [slotValue, h] using P.carrierBound_nonneg
    | some l => simpa [slotValue, h] using P.carrier_bound j l k

@[simp] theorem slotted_length (b : Fin B) (j : Fin N) :
    (P.slotted hcard b).length j = P.length j := rfl

@[simp] theorem slotted_constant (b : Fin B) :
    (P.slotted hcard b).constant = P.constant := rfl

@[simp] theorem slotted_actualX (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualX j p = P.actualX j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originX j) + P.length j * (P.site j p.1.1 p.1.2).1 = _
  rw [P.slotValue_item hcard b j (P.originX j) p]
  rfl

@[simp] theorem slotted_actualZ (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualZ j p = P.actualZ j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originZ j) +
    P.slotValue hcard b j (P.rowSlope j) * P.length j * (P.site j p.1.1 p.1.2).1 +
      P.width * (P.site j p.1.1 p.1.2).2 = _
  rw [P.slotValue_item hcard b j (P.originZ j) p,
    P.slotValue_item hcard b j (P.rowSlope j) p]
  rfl

theorem slotted_rowSlope (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).rowSlope j = P.rowSlope j p.1.1 :=
  P.slotValue_item hcard b j (P.rowSlope j) p

@[simp] theorem slotted_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    (P.slotted hcard b).raw i j p k y = P.raw i j p.1.1 p.1.2 k y := by
  unfold SourceLatticePacket.raw raw
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

@[simp] theorem slotted_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    (P.slotted hcard b).physicalPacket t j p k = P.physicalPacket t j p.1.1 p.1.2 k := by
  unfold SourceLatticePacket.physicalPacket physicalPacket
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

theorem slotted_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ j l u k ξ η,
      planarAngularFourier (P.physicalPacket t j l u k) (ξ, η) ≠ 0 →
        |ξ + (t + P.rowSlope j l) * η| ≤ cStar / P.length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta)
    (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) (ξ η : ℝ) :
    planarAngularFourier ((P.slotted hcard b).physicalPacket t j p k) (ξ, η) ≠ 0 →
      |ξ + (t + (P.slotted hcard b).rowSlope j) * η| ≤
          cStar / (P.slotted hcard b).length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
  simpa only [P.slotted_physicalPacket hcard, P.slotted_rowSlope hcard b j p,
    P.slotted_length hcard] using hspectrum j p.1.1 p.1.2 k ξ η

/-- Selector separation is only needed for existing packets; therefore
it is inherited even when a slot is empty at some scales. -/
theorem slotted_selector (w cb Cb : ℝ)
    (hselector : ∀ j (l : P.labels j) (_u : Item j l),
      cb * w / P.length j ≤ |P.rowSlope j l| ∧
        |P.rowSlope j l| ≤ Cb * w / P.length j)
    (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    cb * w / (P.slotted hcard b).length j ≤ |(P.slotted hcard b).rowSlope j| ∧
      |(P.slotted hcard b).rowSlope j| ≤ Cb * w / (P.slotted hcard b).length j := by
  simpa only [P.slotted_rowSlope hcard b j p, P.slotted_length hcard] using
    hselector j p.1.1 p.1.2

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
