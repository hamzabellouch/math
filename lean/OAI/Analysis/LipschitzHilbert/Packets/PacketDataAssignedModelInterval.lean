import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedPathIntegral

namespace OAI

/-! The complete covariant concentration input passes unchanged to the
inhabited assigned model, retaining the original analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.assignedReferenceFamily packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "selector" => P.assignedReferenceSelector packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

theorem assignedInhabitedRawInterval_original
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (top : τ)
    (jet : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    ((Q top).inhabitedFamily.withProfile ((Q top).inhabitedAlternate (alts alt top))
      ((Q top).inhabitedAlternate_bound (alts alt top) (halt alt hAlt top))).rawInterval
      ((Q top).inhabitedFamily.physicalMultiplierCoefficient (T top).slope
        (fun j l => selector b top j ((Q top).inhabitedOriginalLabel j l)) v f)
      jet lower upper x y =
    ((Q top).withProfile (alts alt top) (halt alt hAlt top)).rawInterval
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
      jet lower upper x y := by
  rw [(Q top).inhabitedFamily_rawInterval_original (alts alt top) (halt alt hAlt top)
    (T top).slope (selector b top) v f jet lower upper hlu x y]
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope (selector b top) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  rw [hcoeff]

end LipschitzHilbert.PacketLatticeData

end

end OAI
