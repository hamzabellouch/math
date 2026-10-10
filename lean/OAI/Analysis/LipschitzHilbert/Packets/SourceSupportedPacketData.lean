import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration

namespace OAI

/-! Raw packet data with length control only on actual retained items. No
concentration conclusion is included in these structures. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
structure SupportedTopRawPacketData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (P : PlanarPacketFamily N κ ι) (lo hi : ℝ) (T : SlopeBox) (K : ℝ) (D : ℕ) where
  raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  frequency : κ → ℝ
  length_le : ∀ j (_u : ι j), P.length j ≤ K*T.length
  width_le : P.width ≤ K*T.width
  centerX_le : ∀ j u, |P.centerX j u-T.x| ≤ K*T.length
  centerZ_le : ∀ j u, |P.centerZ j u-(T.y-T.slope*T.x)| ≤ K*T.width
  wave_eq : ∀ j u k y, raw 0 j u k y = P.wave j u k y
  bound : ∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  derivative_bound : ∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  low : ∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) ξ = 0
  high : ∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (raw i j u k y) ξ = 0
  covariant : ∀ y j u k x, (4*(K*T.width):ℂ)*
    (deriv (fun t => raw 0 j u k t x) y -
      (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x
  continuous : ∀ i j u k, Continuous (fun z : ℝ × ℝ => raw i j u k z.1 z.2)
  differentiable : ∀ j u k x y, DifferentiableAt ℝ (fun t => raw 0 j u k t x) y

structure SupportedTopCovariantData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] {P : PlanarPacketFamily N κ ι}
    {lo hi : ℝ} {T : SlopeBox} {K : ℝ} {D : ℕ}
    (data : SupportedTopRawPacketData P lo hi T K D) where
  second : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  bound : ∀ y j u k x, ‖second j u k y x‖ ≤ P.constant*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  derivative_bound : ∀ y j u k x, ‖deriv (second j u k y) x‖ ≤ (P.constant/P.length j)*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  low : ∀ y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (second j u k y) ξ = 0
  high : ∀ y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (second j u k y) ξ = 0
  covariant : ∀ y j u k x, (4*(K*T.width):ℂ)*
    (deriv (fun t => data.raw 1 j u k t x) y -
      (data.frequency k:ℂ)*Complex.I*data.raw 1 j u k y x) = second j u k y x
  continuous : ∀ j u k, Continuous (fun z : ℝ × ℝ => second j u k z.1 z.2)
  differentiable : ∀ j u k x y, DifferentiableAt ℝ (fun t => data.raw 1 j u k t x) y
structure SourceSupportedLatticeTopGeometry {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
    (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : ∀ j (_u : ι j), P.length j ≤ K*T.length
  width_le : P.width ≤ K*T.width
  centerX_le : ∀ j u, |P.actualX j u-T.x|+P.length j ≤ K*T.length
  centerZ_le : ∀ j u, |P.actualZ j u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width
  order_le : 3+2*(8*D+1) ≤ P.order
  scale_eq : P.scale = 4*(K*T.width)

structure SourceSupportedLabeledTopGeometry {N : ℕ} {κ : Type} {Label : Fin N → Type}
    {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item) (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : ∀ j (l : P.labels j) (_u : Item j l), P.length j ≤ K * T.length
  width_le : P.width ≤ K * T.width
  centerX_le : ∀ j l u, |P.actualX j l u - T.x| + P.length j ≤ K * T.length
  centerZ_le : ∀ j l u,
    |P.actualZ j l u - (T.y - T.slope * T.x)| + P.width ≤ K * T.width
  order_le : 3 + 2 * (8 * D + 1) ≤ P.order
  scale_eq : P.scale = 4 * (K * T.width)

end LipschitzHilbert

end

end OAI
