import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def selectedPhysicalPrefix (Q : Finset P.PacketIndex) (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

theorem selectedPhysicalPrefix_eq_restricted (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z =
      (P.restrictPackets Q).physicalStoppingPrefix (P.restrictedAlternate alt Q)
        (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
        L A stop z := by
  unfold selectedPhysicalPrefix physicalStoppingPrefix
  congr 1
  funext k
  symm
  simp_rw [P.restrictPackets_physicalMaskedValue alt hAlt Q]
  ext i
  simp only [WithLp.ofLp_sum,Finset.sum_apply]
  convert P.sum_restrictPackets_filter Q
    (fun q => P.physicalMaskedValue alt hAlt t b v g T L A z q i)
    (fun q => stop q.1 = k) using 1 <;> congr 1 <;> ext q <;> simp

/-- The original fixed residual subset has the required clamped prefix
bound on its own reference event, for every angular horizon. -/
theorem selectedPhysicalPrefix_good_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : (P.restrictPackets Q).physicalMaskedVariation (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
      L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  rw [P.selectedPhysicalPrefix_eq_restricted alt hAlt t b v g T L A Q stop]
  exact (P.restrictPackets Q).physicalStoppingPrefix_good_bound (P.restrictedAlternate alt Q)
    (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
    L A stop hstop y x H hV

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
