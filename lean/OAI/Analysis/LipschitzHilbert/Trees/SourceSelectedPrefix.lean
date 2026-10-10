import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMaximal

namespace OAI

/-! Distant longer packets in a fixed selected tree form an actual
initial scale segment, so their norm is bounded by its interval maximum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def onPackets (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈S then c j l u else 0

theorem onPackets_nonzero (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l)
    (h : P.onPackets S c j l u≠0) : (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈S := by
  by_contra hn
  exact h (by simp only [onPackets,hn,ite_false])

theorem onPackets_energy_sum (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (∑ j, ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width)=
      ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  have he (q : P.PacketIndex) :
      ‖P.onPackets S c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width=
        if q∈S then ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
    by_cases hq : q∈S <;> simp [onPackets,hq]
  calc
    _ = ∑ q : P.PacketIndex, ‖P.onPackets S c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
      simp only [Fintype.sum_sigma]
    _ = ∑ q : P.PacketIndex, if q∈S then ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0 := by
      simp only [he]
    _ = _ := by
      rw [←Finset.sum_filter]
      congr 1
      ext q
      simp

theorem packetVector_onPackets (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) (z : ℝ×ℝ) :
    P.packetVector (P.onPackets S c) q z=if q∈S then P.packetVector c q z else 0 := by
  by_cases hq : q∈S
  · simp only [packetVector,onPackets,hq,ite_true]
  · simp only [packetVector,onPackets,hq,ite_false,WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    rfl

theorem physicalTreePartial_index_sum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartial 0 c n z=∑ q : P.PacketIndex,
      if q.1.val<n then P.packetVector c q z else 0 := by
  ext k
  simp only [physicalTreePartial,packetPartialSum,WithLp.ofLp_sum,Finset.sum_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val<n
  · simp only [hj,ite_true,planarFixedSynthesis,packetVector,WithLp.ofLp_toLp,Fintype.sum_sigma]
  · simp only [hj,ite_false,WithLp.ofLp_zero,Pi.zero_apply,Finset.sum_const_zero]

theorem selected_partial_eq
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.PacketIndex) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartial 0 (P.onPackets S c) n z=
      ∑ q∈S.filter (fun q => q.1.val<n), P.packetVector c q z := by
  rw [P.physicalTreePartial_index_sum]
  simp_rw [P.packetVector_onPackets]
  calc
    _ = ∑ q : P.PacketIndex, if q∈S ∧ q.1.val<n then P.packetVector c q z else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : q∈S <;> by_cases hn : q.1.val<n <;> simp [hq,hn]
    _ = _ := by
      rw [←Finset.sum_filter]
      congr 1
      ext q
      simp

theorem selected_long_prefix_le_maximal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.PacketIndex) (i : Fin N) (gap : ℕ) (z : ℝ×ℝ) :
    ‖∑ q∈S.filter (fun q => q.1.val+gap≤ i.val), P.packetVector c q z‖≤
      P.physicalTreeMaximal 0 (P.onPackets S c) z := by
  let n := i.val+1-gap
  have hn : n≤N := by dsimp [n]; have := i.isLt; omega
  have he : S.filter (fun q => q.1.val+gap≤ i.val)=S.filter (fun q => q.1.val<n) := by
    ext q
    have ha : q.1.val+gap≤ i.val ↔ q.1.val<(i.val+1)-gap := by omega
    simp only [Finset.mem_filter,n,ha]
  rw [he,←P.selected_partial_eq c S n z]
  have hzero : P.physicalTreePartial 0 (P.onPackets S c) 0 z=0 := by
    simp only [physicalTreePartial,packetPartialSum,not_lt_zero,ite_false,Finset.sum_const_zero]
  have h := increment_le_intervalOscillation
    (fun m => P.physicalTreePartial 0 (P.onPackets S c) m z) N 0 N 0 n
    le_rfl (Nat.zero_le _) hn le_rfl
  simpa only [hzero,sub_zero,physicalTreeMaximal] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
