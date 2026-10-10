import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedFamily

namespace OAI

/-! Packet hypotheses transported once to the selected family, before
applying the analytic tree estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure OrdinaryTreePacketData (P : SourceLabeledLattice N κ Label Item)
    (cStar cEta CEta cb Cb Cv a b w sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) : Prop where
  centerX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2
  centerY : ∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2
  reference : ∀ q : P.PacketIndex, 0∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
  angle : ∀ j l, P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)
  spectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
    |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
  slope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j
  bin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
    |η-P.frequency k|≤Cv/P.width
  coefficient : ∀ j l v, ‖c j l v‖≤sigma
  size : P.angularSeparatedTreeEnergy cb w c≤sigma^2*(P.topLength*P.width)

theorem selectedFamily_spectrum (P : SourceLabeledLattice N κ Label Item)
    (Q : Finset P.PacketIndex) (w cStar cEta CEta : ℝ)
    (h : ∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
      |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta) :
    ∀ j l v k ξ η, planarAngularFourier ((P.selectedFamily Q).physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+(P.selectedFamily Q).rowSlope j l*η|≤cStar/(P.selectedFamily Q).length j ∧
        cEta≤w*η ∧ w*η≤CEta := by
  intro j l v k ξ η hn
  rw [P.selectedFamily_physicalPacket] at hn
  change |ξ+P.rowSlope j (P.selectedOriginalLabel Q j l)*η|≤cStar/P.length j ∧
    cEta≤w*η ∧ w*η≤CEta
  exact h ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v) k ξ η hn

theorem selectedFamily_bin (P : SourceLabeledLattice N κ Label Item)
    (Q : Finset P.PacketIndex) (Cv : ℝ)
    (h : ∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
      |η-P.frequency k|≤Cv/P.width) :
    ∀ j l v k ξ η, planarAngularFourier ((P.selectedFamily Q).physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-(P.selectedFamily Q).frequency k|≤Cv/(P.selectedFamily Q).width := by
  intro j l v k ξ η hn
  rw [P.selectedFamily_physicalPacket] at hn
  exact h ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v) k ξ η hn

theorem selectedFamily_coefficient (P : SourceLabeledLattice N κ Label Item)
    (Q : Finset P.PacketIndex) (sigma : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (h : ∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖≤sigma) :
    ∀ j (l : (P.selectedFamily Q).labels j) (v : P.RestrictedPacketItem Q j l),
      ‖c j (P.selectedOriginalLabel Q j l) v.val‖≤sigma := by
  intro j l v
  exact h ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v)

theorem selectedFamily_treeData (P : SourceLabeledLattice N κ Label Item)
    (Q : Finset P.PacketIndex) (cStar cEta CEta cb Cb Cv a b w sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hX : ∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2)
    (href : ∀ q∈Q, 0∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hangle : ∀ q∈Q, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
      grid q.1.val (cell q.1 q.2.1))
    (hspectrum : ∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
      |ξ+P.rowSlope q.1 q.2.1*η|≤cStar/P.length q.1 ∧ cEta≤w*η ∧ w*η≤CEta)
    (hslope : ∀ q∈Q, |P.rowSlope q.1 q.2.1|≤Cb*w/P.length q.1)
    (hbin : ∀ q∈Q, ∀ k ξ η, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (ξ,η)≠0 →
      |η-P.frequency k|≤Cv/P.width)
    (hc : ∀ q∈Q, ‖c q.1 q.2.1 q.2.2‖≤sigma)
    (hsize : (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)≤sigma^2*(P.topLength*P.width)) :
    OrdinaryTreePacketData (P.selectedFamily Q) cStar cEta CEta cb Cb Cv a b w sigma
      (fun j l => cell j (P.selectedOriginalLabel Q j l)) grid
      (fun j l v => c j (P.selectedOriginalLabel Q j l) v.val) := by
  constructor
  · rintro ⟨j,l,v⟩
    change |P.actualX j (P.selectedOriginalLabel Q j l) v.val-a|≤P.topLength/2
    exact hX ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v)
  · rintro ⟨j,l,v⟩
    change |P.actualZ j (P.selectedOriginalLabel Q j l) v.val-b|≤P.width/2
    exact hY ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v)
  · rintro ⟨j,l,v⟩
    exact href ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedFamily_mem Q j l v)
  · intro j l
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet Q j l
    exact hangle ⟨j,⟨P.selectedOriginalLabel Q j l,v⟩⟩ hv
  · exact P.selectedFamily_spectrum Q w cStar cEta CEta hspectrum
  · intro j l
    obtain ⟨v,hv⟩ := P.selectedLabel_has_packet Q j l
    exact hslope ⟨j,⟨P.selectedOriginalLabel Q j l,v⟩⟩ hv
  · exact P.selectedFamily_bin Q Cv hbin
  · exact P.selectedFamily_coefficient Q sigma c hc
  · rw [P.selectedFamily_separated_energy]
    exact hsize

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
