import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedScale
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataRecordedEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleGramSplit
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPacketGram

namespace OAI

/-! Exact far-Gram grouping over the actual selected records, followed
by the global near/far energy assembly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def farPairing (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) : ℂ :=
  ∑ s∈S, ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z)
    ∂volume.prod volume

theorem farPairing_eq_gram
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) :
    P.farPairing c S T gap=∑ s∈S, ∑ q∈T, if q.1.val+gap≤s.1.val then
      inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0 := by
  unfold farPairing
  apply Finset.sum_congr rfl
  intro s _
  simp only [longPacketSum,inner_sum]
  rw [integral_finsetSum _ (fun q _ => P.packetVector_inner_integrable c s q)]
  simp only [Finset.sum_filter,P.packetL2_inner]

theorem selected_far_gram_sum (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (gap : ℕ) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∑ s∈S, ∑ q∈S, if q.1.val+gap≤s.1.val then
      inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0)=
      ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset,
        P.farPairing c S p.2 gap := by
  dsimp only
  calc
    _ = ∑ s∈P.selectedPackets negative w cb A cell grid initial tops,
        ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset,
          ∑ q∈p.2, if q.1.val+gap≤s.1.val then
            inner ℂ (P.packetL2 c s) (P.packetL2 c q) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      exact P.selectedPackets_sum negative w cb A hA cell grid initial tops _
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [P.farPairing_eq_gram]

/-- The exact near/far assembly for a selected set. Its two estimates
follow from local multiplicity and the per-record far theorem. -/
theorem selected_gram_energy
    (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) (gap : ℕ)
    (Cnear Cfar : ℝ)
    (hnear : let S := P.selectedPackets negative w cb A cell grid initial tops
      (∑ s∈S, ∑ q∈S, if |(s.1.val:ℤ)-(q.1.val:ℤ)|≤(gap:ℤ) then
        (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re else 0)≤Cnear*P.packetEnergySum c S)
    (hfar : ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      ‖P.farPairing c (P.selectedPackets negative w cb A cell grid initial tops) p.2 (gap+1)‖≤
        Cfar*P.packetEnergySum c p.2) :
    let S := P.selectedPackets negative w cb A cell grid initial tops
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (Cnear+2*Cfar)*P.packetEnergySum c S := by
  dsimp only at hnear ⊢
  let S := P.selectedPackets negative w cb A cell grid initial tops
  let R := (P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset
  let G := fun s q => (inner ℂ (P.packetL2 c s) (P.packetL2 c q)).re
  have hsym (s q : P.PacketIndex) : G s q=G q s := by
    change RCLike.re (inner ℂ (P.packetL2 c s) (P.packetL2 c q))=
      RCLike.re (inner ℂ (P.packetL2 c q) (P.packetL2 c s))
    exact inner_re_symm _ _
  have hsplit := scale_gram_split S (fun q => q.1.val) G hsym gap
  have hnorm : (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)=
      ∑ s∈S, ∑ q∈S, G s q := by
    rw [←finite_L2_sum_norm_sq _ S _ (P.packetVector_memLp c)]
    change ‖∑ q∈S, P.packetL2 c q‖^2=
      ∑ s∈S, ∑ q∈S, RCLike.re (inner ℂ (P.packetL2 c s) (P.packetL2 c q))
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ]
    simp only [sum_inner,inner_sum,map_sum]
    exact Finset.sum_comm
  have hreal : (∑ s∈S, ∑ q∈S, if q.1.val+gap+1≤s.1.val then G s q else 0)=
      ∑ p∈R, (P.farPairing c S p.2 (gap+1)).re := by
    change (∑ s∈S, ∑ q∈S, if q.1.val+gap+1≤s.1.val then
      (RCLike.re : ℂ → ℝ) (inner ℂ (P.packetL2 c s) (P.packetL2 c q)) else 0)=
      ∑ p∈R, (RCLike.re : ℂ → ℝ) (P.farPairing c S p.2 (gap+1))
    have he := P.selected_far_gram_sum negative w cb A hA cell grid c initial tops (gap+1)
    have hr := congrArg Complex.re he
    change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at hr
    simpa only [R,S,G,map_sum,apply_ite,map_zero,Nat.add_assoc] using hr
  have hb : (∑ p∈R, (P.farPairing c S p.2 (gap+1)).re)≤Cfar*P.packetEnergySum c S := by
    calc
      _ ≤ ∑ p∈R, Cfar*P.packetEnergySum c p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact (Complex.re_le_norm _).trans (hfar p (List.mem_toFinset.mp hp))
      _ = _ := by
        rw [←Finset.mul_sum]
        congr 1
        exact (P.selectedPackets_sum negative w cb A hA cell grid initial tops _).symm
  rw [hnorm,hsplit,hreal]
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
