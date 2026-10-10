import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceLattice
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice

namespace OAI

/-! The fixed reference collection is a literal restriction of the
original labels. Its new reference coordinates keep every selected
profile, integer site and physical packet unchanged. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def referenceLabels (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j,
    P.length j ≤ referenceLength ∧
      |oldSlope+P.rowSlope j ⟨l,h⟩-newSlope| ≤ cone*w/P.length j)

def referenceOriginalLabel (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

theorem referenceLabel_bounds (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) :
    P.length j ≤ referenceLength ∧
      |P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
        (oldSlope-newSlope)| ≤ cone*w/P.length j := by
  obtain ⟨h,hshort,hangle⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) =
      P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l := Subtype.ext rfl
  rw [heq] at hangle
  refine ⟨hshort,?_⟩
  convert hangle using 1
  congr 1
  ring

/-- Only labels in the fixed short reference cone remain. All spatial
items in those labels retain the original lattice and profile. -/
def referenceFamily (oldSlope newSlope referenceLength cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w) : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F*cone
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := mul_nonneg hF hcone
  labels := P.referenceLabels oldSlope newSlope referenceLength cone w
  originX := fun j l => P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  originZ := fun j l =>
    P.originZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)*P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  rowSlope := fun j l =>
    P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope)
  frequency := P.frequency
  site := fun j l => P.site j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  site_injective := fun j l => P.site_injective j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile := fun j l => P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile_bound := fun j l => P.profile_bound j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  shear_bound := by
    intro j l
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    change |(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope))*P.length j/P.width| ≤ 1
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (((le_div_iff₀ (P.length_pos j)).mp h).trans hwide)
  carrier_bound := by
    intro j l k
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    have hr := (le_div_iff₀ (P.length_pos j)).mp h
    change |P.frequency k*(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope))*P.length j| ≤ F*cone
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(cone*w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*cone := by field_simp

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

abbrev RefLabel (j : Fin N) := P.referenceLabels oldSlope newSlope referenceLength cone w j

@[simp] theorem referenceFamily_length (j : Fin N) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).length j =
      P.length j := rfl

@[simp] theorem referenceFamily_actualX (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).actualX j l u =
      P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := rfl

theorem referenceFamily_actualZ (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).actualZ j l u =
      P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
        (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [actualZ,actualX,referenceFamily,length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) (k : κ) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).physicalPacket
      newSlope j l u k =
      P.physicalPacket oldSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  ext z
  simp only [physicalPacket,physicalPlanarPacket_apply]
  rw [P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency,
    P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency]
  have hx : P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u =
      P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
        oldSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by ring
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)) =
      oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by ring
  change Complex.exp (((P.frequency k *
    ((z.2-(P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))-
      (newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)))*(z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))):ℝ)*Complex.I) *
    P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k
      ((z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u)/P.length j,
      ((z.2-(P.actualZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      (oldSlope-newSlope)*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u+
      newSlope*P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))-
      (newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)))*(z.1-P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u))/P.width) = _
  rw [hx,hs]

theorem referenceFamily_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ j (l : P.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(oldSlope+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) :
    let Q := P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
    ∀ j (l : Q.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (Q.physicalPacket newSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(newSlope+Q.rowSlope j l)*η| ≤ cStar/Q.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta := by
  dsimp only
  intro j l u k ξ η hξ
  rw [P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency j l u k] at hξ
  have h := hspectrum j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k ξ η hξ
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)) = oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by ring
  simpa only [referenceFamily,hs,length] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
