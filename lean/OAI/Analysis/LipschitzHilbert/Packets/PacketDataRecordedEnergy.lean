import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedRecordSums

namespace OAI

/-! The strict stopping test gives a lower energy bound for every
recorded top. This is the bound needed to sum its far-Gram estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item}
  {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

namespace SizeStoppingRun

theorem recorded_energy_lower
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops,
      sigma^2*p.1.area≤2*P.packetEnergySum c p.2 := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have ht := hT.2.2.le
      change sigma^2*T.area/2≤P.packetEnergySum c _ at ht
      linarith
    · exact ih p hp

theorem recorded_nonempty
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeSelectionRecords negative w cb A cell grid initial tops, p.2.Nonempty := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
    · exact ih p hp

theorem records_nodup
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    (P.sizeSelectionRecords negative w cb A cell grid initial tops).Nodup := by
  change (P.sizeSelectionRecords negative w cb A cell grid initial tops).Pairwise (· ≠ ·)
  apply (P.sizeSelectionRecords_disjoint negative w cb A hA cell grid initial tops).imp_of_mem
  intro p q hp _ hd hpq
  subst q
  obtain ⟨r,hr⟩ := h.recorded_nonempty p hp
  exact Finset.disjoint_left.mp hd hr hr

theorem selected_energy_eq_records
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    P.packetEnergySum c (P.selectedPackets negative w cb A cell grid initial tops)=
      ((P.recordedSizeTests negative w cb A cell grid initial tops).map (P.packetEnergySum c)).sum := by
  unfold packetEnergySum
  rw [P.selectedPackets_sum negative w cb A hA cell grid initial tops]
  rw [List.sum_toFinset _ (h.records_nodup hA)]
  rw [←P.sizeSelectionRecords_packets negative w cb A cell grid initial tops,List.map_map]
  rfl

end SizeStoppingRun
end LipschitzHilbert.PacketLatticeData

end

end OAI
