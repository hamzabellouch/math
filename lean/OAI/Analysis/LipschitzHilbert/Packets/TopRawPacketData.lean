import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedGlobalNeighborhood
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight

namespace OAI

/-! Local packet data used by the top concentration argument. Every field
is a raw kernel, geometry, regularity, or Fourier-support condition; no
concentration or coefficient-budget assumption is included. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

structure TopRawPacketData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (P : PlanarPacketFamily N κ ι) (lo hi : ℝ) (T : SlopeBox) (K : ℝ) (D : ℕ) where
  raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  frequency : κ → ℝ
  length_le : P.topLength ≤ K*T.length
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

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def topPacketAmplitude (P : PlanarPacketFamily N κ ι) (Ab Am : ℝ) (D : ℕ) : ℝ :=
  let C := topPairConstant P.constant (8*D+1)
  P.coefficientScale*256^(8*D+1)*
    (24*lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) 2)

theorem topPacketAmplitude_pos (P : PlanarPacketFamily N κ ι) (Ab Am : ℝ) (D : ℕ) :
    0 < P.topPacketAmplitude Ab Am D := by
  have hC := topPairConstant_pos P.constant (8*D+1) P.constant_pos
  have hM := lineMomentBase_pos (topPairConstant P.constant (8*D+1))
    (Am*(topPairConstant P.constant (8*D+1))^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1)
    2 hC.le (by norm_num)
  have := P.coefficientScale_pos
  unfold topPacketAmplitude
  positivity

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
