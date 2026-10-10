import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossValue
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossIdentity

namespace OAI

/-! Local reference restriction preserves the actual two-profile packet
operator, including its masked analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0≤cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

abbrev referenceAlt
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ j (l : (Q).labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ :=
  fun j l => alt j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)

theorem referenceAlt_bound
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (k : κ) :
    planarProfileConstant
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt j l a k)
        (2*(Q).order)≤(Q).profileBound :=
  hAlt j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) a k

theorem referenceAlt_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (k : κ) :
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k =
    (P.withProfile alt hAlt).physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) a k := by
  exact (P.withProfile alt hAlt).referenceFamily_physicalPacket
    oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency j l a k

theorem referenceFamily_crossPacketValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (z : ℝ×ℝ) :
    (Q).physicalCrossPacketValue
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
      newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g 0 z ⟨j,l,a⟩ =
    P.crossPacketValue alt hAlt oldSlope b v g z
      ⟨j,P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,a⟩ := by
  have he := (Q).physicalCrossPacketValue_zero
    (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
    (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)
    newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
    v g (z.2-newSlope*z.1) z.1 ⟨j,l,a⟩
  have hz : (z.1,z.2-newSlope*z.1+newSlope*z.1)=z := by
    ext
    · rfl
    · dsimp only
      ring
  rw [hz] at he
  rw [he]
  apply WithLp.ofLp_injective
  funext k
  change (Q).physicalMultiplierCoefficient newSlope
    (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l a k *
    ((Q).withProfile
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt)
      (P.referenceAlt_bound oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt hAlt)).physicalPacket
        newSlope j l a k z = _
  rw [P.referenceFamily_multiplier_coefficient oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency b v g j l a,
    P.referenceAlt_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency alt hAlt j l a k]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
