import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularModel
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataCrossValue

namespace OAI

/-! Exact reconstruction after the three-grid split. The selector for
each piece agrees with the original one on every retained packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sum_angularPackets (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ g : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag g, f a)=
      ∑ a∈initial, f a := by
  simp only [angularPackets,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem crossPacketValue_congr_selector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b c : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (a : P.PacketIndex)
    (h : ∀ k s, b a.1 a.2.1 k s=c a.1 a.2.1 k s) :
    P.crossPacketValue alt hAlt t b u g z a=P.crossPacketValue alt hAlt t c u g z a := by
  have he : b a.1 a.2.1=c a.1 a.2.1 := funext (fun k => funext (h k))
  simp only [crossPacketValue,physicalMultiplierCoefficient,he]

theorem crossPacketValue_angularSelector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (grid : DyadicLineGrid.GridChoice) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (t : ℝ) (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (a : P.PacketIndex) (ha : a∈P.angularPackets initial tag grid) :
    P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a=
      P.crossPacketValue alt hAlt t b u g z a := by
  apply P.crossPacketValue_congr_selector alt hAlt t _ _ u g z a
  intro k s
  simp only [angularSelector,(Finset.mem_filter.mp ha).2,ite_true]

theorem sum_crossPacketValue_angularPartition (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (t : ℝ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
      P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a)=
      ∑ a∈initial, P.crossPacketValue alt hAlt t b u g z a := by
  calc
    _ = ∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
        P.crossPacketValue alt hAlt t b u g z a := by
      apply Finset.sum_congr rfl
      intro grid _
      exact Finset.sum_congr rfl (fun a ha =>
        P.crossPacketValue_angularSelector alt hAlt initial tag grid b t u g z a ha)
    _ = _ := P.sum_angularPackets initial tag _

end LipschitzHilbert.PacketLatticeData

end

end OAI
