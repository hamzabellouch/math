import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedReference
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataMaskedValue

namespace OAI

/-! Exact regrouping of unrestricted physical packets in their assigned
reference families. The analyzing integrals and top masks are unchanged. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem crossSum_eq_rawInterval (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ q : P.PacketIndex, P.physicalCrossPacketValue alt hAlt t b v f 0 z q) =
      (P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v f)
        0 0 N z.1 (z.2-t*z.1) := by
  ext k
  simp only [physicalCrossPacketValue,rawPacketValue,rawInterval,planarPacketInterval,
    bandIntervalSignal,scalarBandPartial,planarPacketBand,WithLp.ofLp_sum,
    WithLp.ofLp_toLp,Finset.sum_apply,Fintype.sum_sigma,Fin.is_lt,ite_true,
    Nat.not_lt_zero,ite_false,Finset.sum_const_zero,sub_zero]

end SourceLabeledLattice
namespace PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0<w) (hcone : 0≤cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.assignedReferenceFamily packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T t R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => P.assignedReferenceAlternate packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T t R cone w F
  hw hcone hF hwide hfrequency alt hAlt

theorem assignedCrossSum_eq_rawInterval (z : ℝ×ℝ) (top : τ)
    (hcondition : ∀ q ∈ packets, assigned q=top →
      P.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1) :
    (∑ q ∈ packets.filter (fun q => assigned q=top), P.crossPacketValue alt hAlt t b v f z q) =
      ((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val)
        0 0 N z.1 (z.2-(T top).slope*z.1) := by
  let A := P.assignedTopFamily packets assigned top
  let a := P.assignedTopAlternate packets assigned alt top
  let ha := P.assignedTopAlternate_bound packets assigned alt hAlt top
  have hcond : ∀ q ∈ (Finset.univ : Finset A.PacketIndex),
      A.referenceCondition t (T top).slope (R top) cone w q.1 q.2.1 := by
    intro q _
    exact hcondition ⟨q.1,q.2.1.val.2,q.2.2.val⟩
      (P.assignedTopItem_mem packets assigned top q.1 q.2.1 q.2.2)
      (P.assignedTopItem_assignment packets assigned top q.1 q.2.1 q.2.2)
  have hs := A.sum_referenceFamily_selected t (T top).slope (R top) cone w F
    hw hcone hF hwide hfrequency Finset.univ (A.crossPacketValue a ha t
      (fun j l => b j l.val.2) v f z) hcond
  simp only [Finset.mem_univ,Finset.filter_true] at hs
  have hterm (q : (Q top).PacketIndex) :
      (Q top).physicalCrossPacketValue (alts top) (halt top) (T top).slope
        (fun j l => b j (orig top j l)) v f 0 z q =
      A.crossPacketValue a ha t (fun j l => b j l.val.2) v f z
        ⟨q.1,A.referenceOriginalLabel t (T top).slope (R top) cone w q.1 q.2.1,q.2.2⟩ := by
    exact A.referenceFamily_crossPacketValue t (T top).slope (R top) cone w F
      hw hcone hF hwide hfrequency a ha (fun j l => b j l.val.2) v f q.1 q.2.1 q.2.2 z
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig top j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient t b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top t
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  calc
    _ = ∑ q : A.PacketIndex, A.crossPacketValue a ha t (fun j l => b j l.val.2) v f z q :=
      (P.sum_assignedTopPackets packets assigned top (P.crossPacketValue alt hAlt t b v f z)).symm
    _ = ∑ q : (Q top).PacketIndex,
        (Q top).physicalCrossPacketValue (alts top) (halt top) (T top).slope
          (fun j l => b j (orig top j l)) v f 0 z q := by
      rw [←hs]
      exact Finset.sum_congr rfl (fun q _ => (hterm q).symm)
    _ = _ := by
      rw [(Q top).crossSum_eq_rawInterval,hcoeff]

omit R cone w F hw hcone hF hwide hfrequency in
 theorem sum_assignedPhysicalMaskedValue (tops : Finset τ)
    (hassigned : ∀ q∈packets, assigned q∈tops) (L A : ℝ) (z : ℝ×ℝ) :
    (∑ q∈packets, P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q) =
    ∑ top∈tops, (T top).mask L A z •
      ∑ q∈packets.filter (fun q => assigned q=top), P.crossPacketValue alt hAlt t b v f z q := by
  rw [←Finset.sum_fiberwise_of_maps_to hassigned]
  apply Finset.sum_congr rfl
  intro top _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqt := (Finset.mem_filter.mp hq).2
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f]
  simp only [hqt]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
