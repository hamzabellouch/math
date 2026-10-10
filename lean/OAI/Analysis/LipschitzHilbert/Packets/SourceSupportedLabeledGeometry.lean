import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLatticeData
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationActive

namespace OAI

/-! Packetwise top geometry survives slotting and frozen-active label
restriction. These operations keep every retained center and length. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The actual packet-center condition already controls retained lengths. -/
theorem supportedTopGeometry {T : SlopeBox} {K : ℝ} {D : ℕ}
    (hwidth : P.width ≤ K*T.width)
    (hx : ∀ j l u, |P.actualX j l u-T.x|+P.length j ≤ K*T.length)
    (hz : ∀ j l u, |P.actualZ j l u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width)) :
    SourceSupportedLabeledTopGeometry P T K D where
  length_le := fun j l u => by linarith [hx j l u,abs_nonneg (P.actualX j l u-T.x)]
  width_le := hwidth
  centerX_le := hx
  centerZ_le := hz
  order_le := horder
  scale_eq := hscale

theorem slotted_supportedTopGeometry
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D)
    (b : Fin B) : SourceSupportedLatticeTopGeometry (P.slotted hcard b) T K D where
  length_le := fun j p => G.length_le j p.1.1 p.1.2
  width_le := G.width_le
  centerX_le := by
    intro j p
    rw [P.slotted_actualX hcard, P.slotted_length hcard]
    exact G.centerX_le j p.1.1 p.1.2
  centerZ_le := by
    intro j p
    rw [P.slotted_actualZ hcard]
    exact G.centerZ_le j p.1.1 p.1.2
  order_le := G.order_le
  scale_eq := G.scale_eq

theorem activeMainFamily_supportedTopGeometry
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
    (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D) :
    SourceSupportedLabeledTopGeometry
      (P.activeMainFamily t b w F Cb hw hF hCb hfreq hangle) T K D where
  length_le := fun j l u => G.length_le j (P.frozenActiveOriginalLabel t b j l) u
  width_le := G.width_le
  centerX_le := fun j l u => G.centerX_le j (P.frozenActiveOriginalLabel t b j l) u
  centerZ_le := fun j l u => G.centerZ_le j (P.frozenActiveOriginalLabel t b j l) u
  order_le := G.order_le
  scale_eq := G.scale_eq

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
