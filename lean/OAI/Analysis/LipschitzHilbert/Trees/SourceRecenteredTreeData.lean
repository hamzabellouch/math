import OAI.Analysis.LipschitzHilbert.Trees.SourceRecenterTransport

namespace OAI

/-! The packet data of a recentered family is derived from its original
packets. The scalar frequency carrier is controlled separately. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure ReferenceTreePacketData (P : SourceLabeledLattice N κ Label Item)
    (t cStar cEta CEta cb Cb Cv a b w sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) : Prop where
  centerX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2
  centerY : ∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2
  reference : ∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
  angle : ∀ j l, t+P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)
  spectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
    |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
  slope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j
  bin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
    |η-P.frequency k|≤Cv/P.width
  coefficient : ∀ j l v, ‖c j l v‖≤sigma
  size : P.angularSeparatedTreeEnergy cb w c≤sigma^2*(P.topLength*P.width)


theorem recentered_treeData (P : SourceLabeledLattice N κ Label Item)
    (t M cStar cEta CEta cb Cb Cv a b w sigma : ℝ) (hM : 0≤M)
    (hshear : ∀ j l, |(P.rowSlope j l-t)*P.length j/P.width|≤1)
    (hcarrier : ∀ j l k, |P.frequency k*(P.rowSlope j l-t)*P.length j|≤M)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2)
    (href : ∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hangle : ∀ j l, P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta)
    (hslope : ∀ j l, |P.rowSlope j l-t|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-P.frequency k|≤Cv/P.width)
    (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (hsize : (∑ j, ∑ l : P.labels j, ∑ v : Item j l,
      if cb*w/P.length j≤|P.rowSlope j l-t| then ‖c j l v‖^2*P.length j*P.width else 0)≤
      sigma^2*(P.topLength*P.width)) :
    ReferenceTreePacketData (P.recenter t M hM hshear hcarrier) t cStar cEta CEta cb Cb Cv
      a b w sigma cell grid c := by
  constructor
  · rintro ⟨j,l,v⟩
    exact hX ⟨j,⟨l,v⟩⟩
  · rintro ⟨j,l,v⟩
    change P.labels j at l
    change |(P.recenter t M hM hshear hcarrier).actualZ j l v-b|≤P.width/2
    rw [P.recenter_actualZ]
    exact hY ⟨j,⟨l,v⟩⟩
  · exact href
  · intro j l
    change t+(P.rowSlope j l-t)∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)
    simpa only [add_sub_cancel] using hangle j l
  · intro j l v k ξ η hn
    have he : ((P.recenter t M hM hshear hcarrier).physicalPacket t j l v k : ℝ×ℝ → ℂ)=
        P.physicalPacket 0 j l v k := by
      funext z
      exact P.recenter_physicalPacket_reference t M hM hshear hcarrier j l v k z
    rw [he] at hn
    change |ξ+(t+(P.rowSlope j l-t))*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
    simpa only [add_sub_cancel] using hspectrum j l v k ξ η hn
  · exact hslope
  · intro j l v k ξ η hn
    have he : ((P.recenter t M hM hshear hcarrier).physicalPacket t j l v k : ℝ×ℝ → ℂ)=
        P.physicalPacket 0 j l v k := by
      funext z
      exact P.recenter_physicalPacket_reference t M hM hshear hcarrier j l v k z
    rw [he] at hn
    exact hbin j l v k ξ η hn
  · exact hc
  · exact hsize

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
