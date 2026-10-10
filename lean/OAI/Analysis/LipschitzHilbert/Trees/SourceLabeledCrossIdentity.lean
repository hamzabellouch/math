import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossResidual
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledStoppingVariation

namespace OAI

/-! The residual-square and unary-variation estimates use exactly the
same original analyzing coefficients and alternate physical synthesis.
The mask is applied to the synthesized vector, with no coefficient change. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalCrossPacketValue_zero (y x : ℝ) (q : P.PacketIndex) :
    P.physicalCrossPacketValue alt hAlt t b v g 0 (x,y+t*x) q =
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x)) := by
  ext k
  have hw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 q.1 q.2.1 q.2.2 k y t)
  change (P.withProfile alt hAlt).raw 0 q.1 q.2.1 q.2.2 k y x =
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k (x,y+t*x) at hw
  have hy : (y+t*x)-t*x = y := by ring
  simp only [physicalCrossPacketValue,rawPacketValue,WithLp.ofLp_toLp,hy,hw]

theorem physicalMaskedValue_eq_cross
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q =
      (T q.1 q.2.1 q.2.2).mask L A (x,y+t*x) •
        P.physicalCrossPacketValue alt hAlt t b v g 0 (x,y+t*x) q := by
  rw [P.physicalCrossPacketValue_zero alt hAlt t b v g]
  ext k
  simp only [physicalMaskedValue,WithLp.ofLp_toLp,PiLp.smul_apply,Complex.real_smul]
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
