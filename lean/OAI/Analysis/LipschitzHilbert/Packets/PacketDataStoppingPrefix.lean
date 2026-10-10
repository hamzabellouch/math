import OAI.Analysis.LipschitzHilbert.Packets.PacketDataMaskedValue

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def selectedPhysicalPrefix (Q : Finset P.PacketIndex) (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
