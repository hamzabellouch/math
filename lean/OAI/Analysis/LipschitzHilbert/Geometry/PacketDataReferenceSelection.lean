import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity
import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularAssignment
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient

namespace OAI

/-! A finite portion of an unrestricted packet family inside a reference
cone embeds into the bounded reference lattice without changing a wave.
This is the bridge used after a density keeper has been selected. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_bounds_of_density_cell (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w cone : ℝ)
    (hw : 0<w) (hcone : 1≤cone) (q : P.PacketIndex) (T : SlopeBox)
    (hshort : P.length q.1≤T.length)
    (hrow : oldSlope+P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    P.length q.1≤T.length ∧
      |oldSlope+P.rowSlope q.1 q.2.1-T.slope|≤cone*w/P.length q.1 := by
  refine ⟨hshort,?_⟩
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (q.1.val:ℤ)) ⟨oldSlope+P.rowSlope q.1 q.2.1,hrow,hrow⟩ hrow htop
  rw [←P.precision_eq_scaled_grid w q.1] at hs
  apply hs.trans
  apply div_le_div_of_nonneg_right _ (P.length_pos q.1).le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcone hw.le

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0≤cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

def referencePacket (q : P.PacketIndex)
    (hshort : P.length q.1≤referenceLength)
    (hangle : |oldSlope+P.rowSlope q.1 q.2.1-newSlope|≤cone*w/P.length q.1) :
    (Q).PacketIndex :=
  ⟨q.1,⟨⟨q.2.1.val,Finset.mem_filter.mpr ⟨q.2.1.property,
    ⟨q.2.1.property,hshort,hangle⟩⟩⟩,q.2.2⟩⟩

def originalPacket (q : (Q).PacketIndex) : P.PacketIndex :=
  ⟨q.1,⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w q.1 q.2.1,q.2.2⟩⟩

@[simp] theorem original_referencePacket (q : P.PacketIndex)
    (hshort : P.length q.1≤referenceLength)
    (hangle : |oldSlope+P.rowSlope q.1 q.2.1-newSlope|≤cone*w/P.length q.1) :
    P.originalPacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
      (P.referencePacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
        q hshort hangle) = q := rfl

theorem referencePacket_physical (q : P.PacketIndex)
    (hshort : P.length q.1≤referenceLength)
    (hangle : |oldSlope+P.rowSlope q.1 q.2.1-newSlope|≤cone*w/P.length q.1) (k : κ) :
    let r := P.referencePacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
      q hshort hangle
    (Q).physicalPacket newSlope r.1 r.2.1 r.2.2 k =
      P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k := by
  rcases q with ⟨j,l,u⟩
  let label : (Q).labels j := ⟨l.val,Finset.mem_filter.mpr
    ⟨l.property,⟨l.property,hshort,hangle⟩⟩⟩
  exact P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j label u k

variable (S : Finset P.PacketIndex)
  (hS : ∀ q∈S, P.length q.1≤referenceLength ∧
    |oldSlope+P.rowSlope q.1 q.2.1-newSlope|≤cone*w/P.length q.1)

def referencePacketEmbedding : S ↪ (Q).PacketIndex where
  toFun q := P.referencePacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
    q.val (hS q.val q.property).1 (hS q.val q.property).2
  inj' := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg (P.originalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency) hab
    exact h

def referencePackets : Finset (Q).PacketIndex :=
  S.attach.map (P.referencePacketEmbedding oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency S hS)

theorem referencePackets_sum {E : Type*} [AddCommMonoid E] (f : (Q).PacketIndex → E) :
    (∑ r∈P.referencePackets oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency S hS,
      f r) =
    ∑ q : S, f (P.referencePacket oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency
      q.val (hS q.val q.property).1 (hS q.val q.property).2) := by
  simp only [referencePackets,Finset.sum_map,referencePacketEmbedding,Finset.attach_eq_univ]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
