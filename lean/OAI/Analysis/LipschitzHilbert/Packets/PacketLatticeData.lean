import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

structure PacketLatticeData (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
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

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originX j l + P.length j * (P.site j l u).1

def actualZ (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originZ j l + P.rowSlope j l * P.length j * (P.site j l u).1 +
    P.width * (P.site j l u).2

def physicalPacket (t : ℝ) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  physicalPlanarPacket (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u + t * P.actualX j l u) (P.length j) P.width
    (t + P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

def referenceLabels (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j,
    P.length j ≤ referenceLength ∧
      |oldSlope + P.rowSlope j ⟨l,h⟩ - newSlope| ≤ cone * w / P.length j)

def referenceOriginalLabel (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) : P.labels j :=
  ⟨l.val, (Finset.mem_filter.mp l.property).1⟩

theorem referenceLabel_bounds (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) :
    P.length j ≤ referenceLength ∧
      |P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
        (oldSlope - newSlope)| ≤ cone * w / P.length j := by
  obtain ⟨h, hshort, hangle⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) =
      P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l := Subtype.ext rfl
  rw [heq] at hangle
  refine ⟨hshort, ?_⟩
  convert hangle using 1
  congr 1
  ring

/-- The reference lattice derives both dimensionless bounds from its
cone. No bound on the slopes of the original packet family is used. -/
def referenceFamily (oldSlope newSlope referenceLength cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F / w) : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F * cone
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
    P.originZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
      (oldSlope - newSlope) * P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  rowSlope := fun j l =>
    P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) + (oldSlope - newSlope)
  frequency := P.frequency
  site := fun j l => P.site j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  site_injective := fun j l => P.site_injective j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile := fun j l => P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile_bound := fun j l => P.profile_bound j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  shear_bound := by
    intro j l
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    change |(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
      (oldSlope - newSlope)) * P.length j / P.width| ≤ 1
    rw [abs_div, abs_mul, abs_of_pos (P.length_pos j), abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (((le_div_iff₀ (P.length_pos j)).mp h).trans hwide)
  carrier_bound := by
    intro j l k
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    have hr := (le_div_iff₀ (P.length_pos j)).mp h
    change |P.frequency k * (P.rowSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
        (oldSlope - newSlope)) * P.length j| ≤ F * cone
    rw [abs_mul, abs_mul, abs_of_pos (P.length_pos j), mul_assoc]
    calc
      _ ≤ (F / w) * (cone * w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F * cone := by field_simp

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

@[simp] theorem referenceFamily_length (j : Fin N) : (Q).length j = P.length j := rfl

@[simp] theorem referenceFamily_actualX (j : Fin N)
    (l : (Q).labels j) (u : Item j l) :
    (Q).actualX j l u = P.actualX j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := rfl

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
