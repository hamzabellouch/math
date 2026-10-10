import OAI.Analysis.LipschitzHilbert.Packets.TopRawPacketData

namespace OAI

/-! A second raw covariant wave supplies the neighborhood estimate for
the first covariant derivative, while the analyzing coefficients stay fixed. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

structure TopCovariantData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] {P : PlanarPacketFamily N κ ι}
    {lo hi : ℝ} {T : SlopeBox} {K : ℝ} {D : ℕ}
    (data : TopRawPacketData P lo hi T K D) where
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

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_scaled_covariant_eq
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave replacement : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (frequency : κ → ℝ) (s : ℝ) (a b : ℕ) (x y : ℝ)
    (hd : ∀ j u k t, DifferentiableAt ℝ (fun z => wave j u k z x) t)
    (hcov : ∀ j u k, (s:ℂ)*(deriv (fun z => wave j u k z x) y -
      (frequency k:ℂ)*Complex.I*wave j u k y x) = replacement j u k y x) :
    s • covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
      planarPacketInterval coeff replacement a b x y := by
  rw [planarPacketInterval_covariant coeff wave frequency a b x y hd,
    ← planarPacketInterval_smul]
  exact planarPacketInterval_congr_at coeff _ replacement a b x y hcov

end LipschitzHilbert

end

end OAI
