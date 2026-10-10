import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopEnvelope
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopBands
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopReference
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopSelector
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceBand

namespace OAI

/-! Only nonempty assigned scales impose a reference length restriction. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (T : τ → SlopeBox)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w

/-- Empty long scales impose no artificial restriction on the global
longest-scale field. Every retained packet has the true assigned length. -/
theorem assignedTopReference_supported_length
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (j : Fin N) (l : (Q).labels j) (u : P.AssignedTopItem packets assigned j l) :
    (Q).length j ≤ (T top).length := by
  have h := hshort ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
  have ht := P.assignedTopItem_assignment packets assigned top j (orig j l) u
  change P.length j ≤ (T top).length
  simpa only [ht] using h


/-- The supported assigned/reference bands remain the original physical
synthesis with its original top mask, including empty scales. -/
theorem assignedTopReference_topMaskBand_all
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope R cone w q.1 q.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L maskExponent : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (Q).physicalMaskedBand
      (fun j l u k => alt j (orig j l).val.2 u.val k)
      (fun j l u k => hAlt j (orig j l).val.2 u.val k)
      (T top).slope (fun j l => b j (orig j l).val.2) v f
      (fun _ _ _ => T top) L maskExponent (z.2-(T top).slope*z.1) j z.1 =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent packets assigned z (top,j) := by
  have href := (P.assignedTopFamily packets assigned top).referenceFamily_physicalMaskedBand_all
    oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopFamily_referenceCondition packets assigned top oldSlope (T top).slope
      R cone w hcondition)
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top)
    (P.assignedTopSelector packets assigned top b) v f (fun _ _ _ => T top) L maskExponent z j
  exact href.trans (P.assignedTopFamily_topMaskBand packets assigned alt hAlt top oldSlope
    b v f T L maskExponent z j)


/-- The joint estimate returned by assigned-top concentration supplies
the interval premise of the supported envelope and off-child lemmas. -/
theorem assignedTopReference_interval_norm_of_joint
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (A Kw D : ℝ) (z : ℝ×ℝ)
    (hjoint : ∀ lower upper, lower ≤ upper → upper ≤ N →
      let V := fun x y => ((Q).withProfile
        (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
          j (orig j l).val.2 u.val) 0 lower upper x y
      ‖V z.1 (z.2-(T top).slope*z.1)‖+(T top).width*
        ‖covariantSignal P.frequency (fun k y => V z.1 y k) (z.2-(T top).slope*z.1)‖ ≤
          A*((T top).weight Kw D z)^8) :
    ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).rawInterval
        ((Q).physicalMultiplierCoefficient (T top).slope
          (fun j l => b j (orig j l).val.2) v f) 0 lower upper
        z.1 (z.2-(T top).slope*z.1)‖ ≤ A*((T top).weight Kw D z)^8 := by
  intro lower upper hlu hu
  have hcoeff : (Q).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig j l).val.2) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top
      oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency b v f j l u
  rw [hcoeff]
  have h := hjoint lower upper hlu hu
  exact (le_add_of_nonneg_right (mul_nonneg (T top).width_pos.le (norm_nonneg _))).trans h

end LipschitzHilbert.PacketLatticeData

end

end OAI
