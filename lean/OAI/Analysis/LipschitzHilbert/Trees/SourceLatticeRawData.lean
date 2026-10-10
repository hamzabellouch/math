import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.TopCovariantData

namespace OAI

/-! Construct the top concentration data from actual source packets.
The premises describe physical spectrum, actual centers and fixed-order
profile bounds; neither concentration nor a coefficient budget is assumed. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

structure SourceLatticeSpectralData (P : SourceLatticePacket N κ ι) where
  referenceSlope : ℝ
  w : ℝ
  cStar : ℝ
  cEta : ℝ
  CEta : ℝ
  cb : ℝ
  Cb : ℝ
  w_pos : 0 < w
  cEta_pos : 0 < cEta
  cb_nonneg : 0 ≤ cb
  Cb_nonneg : 0 ≤ Cb
  spectrum : ∀ j u k ξ η,
    planarAngularFourier (P.physicalPacket referenceSlope j u k) (ξ,η) ≠ 0 →
      |ξ+(referenceSlope+P.rowSlope j)*η| ≤ cStar/P.length j ∧
        cEta ≤ w*η ∧ w*η ≤ CEta
  selector : ∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j| ∧
    |P.rowSlope j| ≤ Cb*w/P.length j

namespace SourceLatticeSpectralData
variable {P : SourceLatticePacket N κ ι}

def lo (S : SourceLatticeSpectralData P) : ℝ := (S.cEta*S.cb-S.cStar)/(2*Real.pi)
def hi (S : SourceLatticeSpectralData P) : ℝ := (S.CEta*S.Cb+S.cStar)/(2*Real.pi)

theorem raw_cutoffs (S : SourceLatticeSpectralData P)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ ξ, |ξ| < (S.lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (S.hi/P.topLength)*(2:ℝ)^j.val < |ξ| → 𝓕 (P.raw i j u k y) ξ = 0) :=
  P.raw_fourier_cutoffs S.referenceSlope S.w S.cStar S.cEta S.CEta S.cb S.Cb
    S.w_pos S.cEta_pos S.cb_nonneg S.Cb_nonneg S.spectrum S.selector i j u k y

end SourceLatticeSpectralData

structure SourceLatticeTopGeometry (P : SourceLatticePacket N κ ι)
    (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : P.topLength ≤ K*T.length
  width_le : P.width ≤ K*T.width
  centerX_le : ∀ j u, |P.actualX j u-T.x|+P.length j ≤ K*T.length
  centerZ_le : ∀ j u, |P.actualZ j u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width
  order_le : 3+2*(8*D+1) ≤ P.order
  scale_eq : P.scale = 4*(K*T.width)

namespace SourceLatticePacket
variable (P : SourceLatticePacket N κ ι)

theorem raw_top_bound (D : ℕ) (horder : 3+2*(8*D+1) ≤ P.order)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant*
      (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) x *
        lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
  apply (P.raw_bound i j u k y x).trans
  rw [family_centerX,family_centerZ]
  apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_antitone _ _ _ (by omega)) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

theorem raw_top_derivative_bound (D : ℕ) (horder : 3+2*(8*D+1) ≤ P.order)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.constant/P.length j)*
      (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) x *
        lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
  apply (P.raw_derivative_bound i j u k y x).trans
  rw [family_centerX,family_centerZ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_antitone _ _ _ (by omega)) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

def topRawData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceLatticeTopGeometry P T K D) :
    TopRawPacketData P.family (S.lo/P.topLength) (S.hi/P.topLength) T K D where
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

def topCovariantData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceLatticeTopGeometry P T K D) : TopCovariantData (P.topRawData S T K D G) where
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
