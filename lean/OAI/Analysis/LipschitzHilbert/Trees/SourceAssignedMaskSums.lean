import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedBoundaryPrefix
import OAI.Analysis.LipschitzHilbert.Trees.SourceOriginalPathRegularity

namespace OAI

/-! Exact regrouping of the unmasked original packets and of their
assigned top masks. The analyzing coefficient and alternate synthesis
profile are retained in both sums. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

@[simp] theorem SlopeBox.mask_zero (T : SlopeBox) (A : ℝ) (z : ℝ×ℝ) :
    T.mask 0 A z = 1 := by
  simp [SlopeBox.mask,topSincMask,sincProductMask]

namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalMaskedValue_eq_cross_at
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (z : ℝ×ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v f T L A z q =
      (T q.1 q.2.1 q.2.2).mask L A z •
        P.physicalCrossPacketValue alt hAlt t b v f 0 z q := by
  have hz : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp; ring
  simpa only [hz] using P.physicalMaskedValue_eq_cross alt hAlt t b v f T L A
    (z.2-t*z.1) z.1 q

@[simp] theorem physicalMaskedValue_zero
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A : ℝ)
    (z : ℝ×ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v f T 0 A z q =
      P.physicalCrossPacketValue alt hAlt t b v f 0 z q := by
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f T 0 A z q,
    SlopeBox.mask_zero,one_smul]

theorem physicalCrossPacketValue_continuous (q : P.PacketIndex) :
    Continuous (fun z => P.physicalCrossPacketValue alt hAlt t b v f 0 z q) := by
  have hz (z : ℝ×ℝ) : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp; ring
  have heq (z : ℝ×ℝ) := P.physicalCrossPacketValue_zero alt hAlt t b v f
    (z.2-t*z.1) z.1 q
  simp only [hz] at heq
  simp_rw [heq]
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact continuous_const.mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

variable (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.assignedReferenceFamily packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => P.assignedReferenceAlternate packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt hAlt

/-- Removing the neutral mask from the already proved exact interval
identity gives the unmasked original adjoint sum, without division by a mask. -/
theorem assignedCrossInterval_eq_rawInterval (z : ℝ×ℝ) (top : τ)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1)
    (lower upper : ℕ) (hlu : lower ≤ upper) :
    (∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
      P.physicalCrossPacketValue alt hAlt t b v f 0 z q) =
      ((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1) := by
  simpa only [P.physicalMaskedValue_zero,SlopeBox.mask_zero,one_smul] using
    P.assignedPhysicalInterval_eq_maskedRawInterval packets assigned T t R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f 0 0 z top hcondition lower upper hlu

theorem assignedCrossSum_eq_rawInterval (z : ℝ×ℝ) (top : τ)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1) :
    (∑ q ∈ packets.filter (fun q => assigned q = top),
      P.physicalCrossPacketValue alt hAlt t b v f 0 z q) =
      ((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val)
        0 0 N z.1 (z.2-(T top).slope*z.1) := by
  have hfilter : packets.filter (fun q => assigned q = top ∧ 0 ≤ q.1.val ∧ q.1.val < N) =
      packets.filter (fun q => assigned q = top) := by
    ext q
    simp only [Finset.mem_filter,Nat.zero_le,Fin.is_lt,and_true]
  rw [←hfilter]
  exact P.assignedCrossInterval_eq_rawInterval alt hAlt t b v f packets assigned T R cone w F
    hw hcone hF hwide hfrequency z top hcondition 0 N (Nat.zero_le _)

/-- The masked finite sum is exactly the sum of the same original
assigned top sums multiplied by their masks. -/
theorem sum_assignedPhysicalMaskedValue (tops : Finset τ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops) (L A : ℝ) (z : ℝ×ℝ) :
    (∑ q ∈ packets, P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q) =
    ∑ top ∈ tops, (T top).mask L A z •
      ∑ q ∈ packets.filter (fun q => assigned q = top),
        P.physicalCrossPacketValue alt hAlt t b v f 0 z q := by
  rw [←Finset.sum_fiberwise_of_maps_to hassigned]
  apply Finset.sum_congr rfl
  intro top _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqt := (Finset.mem_filter.mp hq).2
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f]
  simp only [hqt]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
