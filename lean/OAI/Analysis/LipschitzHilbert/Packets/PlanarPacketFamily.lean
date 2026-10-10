import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceCarleson
import OAI.Analysis.LipschitzHilbert.Packets.ShortPacketBoxes

namespace OAI

/-! The planar dyadic packet family and its restriction to an actual
short-packet center box. This restriction carries no coefficient budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

structure PlanarPacketFamily (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  topLength : ℝ
  width : ℝ
  constant : ℝ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  constant_pos : 0 < constant
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  wave_measurable : ∀ j i k, Measurable (fun z : ℝ × ℝ => wave j i k z.1 z.2)
  wave_bound : ∀ j i k y x, ‖wave j i k y x‖ ≤ constant *
    (lineEnvelope (baseX + (topLength/(2:ℝ)^j.val) * (site j i).1)
      (topLength/(2:ℝ)^j.val) 3 x *
     lineEnvelope (baseZ + width * (site j i).2) width 3 y)

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def length (P : PlanarPacketFamily N κ ι) (j : Fin N) : ℝ := P.topLength / (2:ℝ)^j.val

def centerX (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseX + P.length j * (P.site j i).1

def centerZ (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseZ + P.width * (P.site j i).2

theorem length_pos (P : PlanarPacketFamily N κ ι) (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def boxIndex (P : PlanarPacketFamily N κ ι) (u y r : ℝ) : ∀ j, ι j → ℤ × ℤ :=
  centerBoxIndex P.centerX P.centerZ u y r P.width

abbrev BoxFiber (P : PlanarPacketFamily N κ ι) (u y r : ℝ) (b : ℤ × ℤ) :=
  ShortBoxFiber P.length (P.boxIndex u y r) r b

def referenceBox (P : PlanarPacketFamily N κ ι) (u y r : ℝ) (hr : 0 < r)
    (b : ℤ × ℤ) : ReferencePacketFamily N κ (P.BoxFiber u y r b) where
  baseX := P.baseX
  baseZ := P.baseZ
  centerX := u+r*b.1
  centerZ := y+P.width*b.2
  radius := r
  width := P.width
  constant := P.constant
  radius_pos := hr
  width_pos := P.width_pos
  length := P.length
  length_pos := P.length_pos
  length_le := fun _ i => i.property.1
  site := fun j i => P.site j i.val
  site_injective := fun j => (P.site_injective j).comp Subtype.val_injective
  center_x := by
    intro j i
    have h := packetBoxIndex_horizontal u y r P.width (P.centerX j i) (P.centerZ j i) hr
    have hi := congrArg Prod.fst i.property.2
    change (packetBoxIndex u y r P.width (P.centerX j i) (P.centerZ j i)).1 = b.1 at hi
    rw [hi] at h
    exact h
  center_z := by
    intro j i
    have h := packetBoxIndex_vertical u y r P.width (P.centerX j i) (P.centerZ j i) P.width_pos
    have hi := congrArg Prod.snd i.property.2
    change (packetBoxIndex u y r P.width (P.centerX j i) (P.centerZ j i)).2 = b.2 at hi
    rw [hi] at h
    exact h
  wave := fun j i k => P.wave j i k
  wave_bound := fun j i k y x => P.wave_bound j i k y x

def selectedWave (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d s.1 then P.wave s.1 s.2 k z.1 z.2 else 0

def mainCoefficient (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (i : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
    (P.selectedWave d v) g ⟨j,i⟩

theorem referenceBox_coefficient (P : PlanarPacketFamily N κ ι) (u y r : ℝ)
    (hr : 0 < r) (b : ℤ × ℤ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (i : P.BoxFiber u y r b j) :
    (P.referenceBox u y r hr b).mainCoefficient d v g j i = P.mainCoefficient d v g j i := rfl

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
