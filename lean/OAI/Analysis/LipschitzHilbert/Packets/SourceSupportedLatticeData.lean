import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedPacketData

namespace OAI

/-! Construct supported raw data from the original physical packet spectrum
and center bounds; empty scales impose no top-length condition. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
def supportedTopRawData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceSupportedLatticeTopGeometry P T K D) :
    SupportedTopRawPacketData P.family (S.lo/P.topLength) (S.hi/P.topLength) T K D where
  raw := fun i => P.raw (i.castLE (by decide))
  frequency := P.frequency
  length_le := G.length_le
  width_le := G.width_le
  centerX_le := fun j u => P.family_centerX_local j u T.x (K*T.length) (G.centerX_le j u)
  centerZ_le := fun j u => P.family_centerZ_local j u (T.y-T.slope*T.x)
    (K*T.width) (G.centerZ_le j u)
  wave_eq := fun _ _ _ _ => rfl
  bound := fun i y j u k x => P.raw_top_bound D G.order_le _ j u k y x
  derivative_bound := fun i y j u k x => P.raw_top_derivative_bound D G.order_le _ j u k y x
  low := fun i y j u k => (S.raw_cutoffs _ j u k y).1
  high := fun i y j u k => (S.raw_cutoffs _ j u k y).2
  covariant := by
    intro y j u k x
    have hs := congrArg Complex.ofReal G.scale_eq
    push_cast at hs
    rw [← hs]
    exact modulatedPlanarJet_covariant_zero (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x
  continuous := by
    intro i j u k
    exact modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale (P.length_pos j).ne' _
  differentiable := by
    intro j u k x y
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' 0 x

def supportedTopCovariantData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceSupportedLatticeTopGeometry P T K D) : SupportedTopCovariantData (P.supportedTopRawData S T K D G) where
  second := P.raw 2
  bound := fun y j u k x => P.raw_top_bound D G.order_le 2 j u k y x
  derivative_bound := fun y j u k x => P.raw_top_derivative_bound D G.order_le 2 j u k y x
  low := fun y j u k => (S.raw_cutoffs 2 j u k y).1
  high := fun y j u k => (S.raw_cutoffs 2 j u k y).2
  covariant := by
    intro y j u k x
    have hs := congrArg Complex.ofReal G.scale_eq
    push_cast at hs
    rw [← hs]
    exact modulatedPlanarJet_covariant_one (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x
  continuous := by
    intro j u k
    exact modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale (P.length_pos j).ne' 2
  differentiable := by
    intro j u k x y
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' 1 x

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
