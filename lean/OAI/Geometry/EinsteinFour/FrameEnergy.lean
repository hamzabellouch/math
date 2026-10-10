import OAI.Geometry.EinsteinFour.FrameAverages
import OAI.Geometry.EinsteinFour.FrameOrientation
import OAI.Geometry.EinsteinFour.AngularEnergy

namespace OAI

/-! Integrate the two actual Weyl derivative energies before applying the
radial comparison. The differential inputs are precisely the integrated
Weyl equations of Gursky--LeBrun (1999), equation (12), p.8, in Ric=3g
normalization. The spherical disintegration and its generic frame-change
premises contain no derivative-energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance frameEnergyNormedAddCommGroup : NormedAddCommGroup Mat3 :=
  Matrix.frobeniusNormedAddCommGroup

def plusGradientEnergy {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  gradientSquareNorm (plusWeylGradient g c (o.frame c))

def minusGradientEnergy {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  gradientSquareNorm (minusWeylGradient g c (o.frame c))

theorem frame_derivative_energy_le
    (g : SmoothMetric M) (o : FrameOrientation g)
    {μ : Measure (FrameBundle g)} (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (σ τ : M → ℝ)
    (hHi : Integrable (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) μ)
    (hZi : Integrable (plusGradientEnergy o) (normalizedVolume g))
    (hWi : Integrable (minusGradientEnergy o) (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2))
    (hturn : ∀ c (e : OrthonormalFrame g c) q,
      frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q)
    (hsym : ∀ c (e : OrthonormalFrame g c) a,
      (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (htr : ∀ c (e : OrthonormalFrame g c) a, (plusWeylGradient g c e a).trace = 0)
    (hE : ∀ c (e : OrthonormalFrame g c),
      gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e) =
          plusGradientEnergy o c + minusGradientEnergy o c)
    (hsum : ∀ c, plusNorm o c + minusNorm o c ≤ 2)
    (hσ : ∀ c, σ c ≤ 1) (hτ : ∀ c, τ c ≤ 1)
    (hvi : Integrable (fun c => plusNorm o c ^ 2) (normalizedVolume g))
    (hbi : Integrable (fun c => minusNorm o c ^ 2) (normalizedVolume g))
    (hci : Integrable (fun c => σ c * plusNorm o c ^ 3 - plusNorm o c ^ 2)
      (normalizedVolume g))
    (hdi : Integrable (fun c => τ c * minusNorm o c ^ 3 - minusNorm o c ^ 2)
      (normalizedVolume g))
    (hZ : (∫ c, plusGradientEnergy o c ∂normalizedVolume g) =
      36 * (∫ c, σ c * plusNorm o c ^ 3 - plusNorm o c ^ 2 ∂normalizedVolume g))
    (hW : (∫ c, minusGradientEnergy o c ∂normalizedVolume g) =
      36 * (∫ c, τ c * minusNorm o c ^ 3 - minusNorm o c ^ 2 ∂normalizedVolume g)) :
    (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤
      (9 / 4) * (∫ c, plusNorm o c ^ 2 + minusNorm o c ^ 2 ∂normalizedVolume g) := by
  have hmean := frameCurvatureDerivative_mean_square g hμ h
    (fun c => plusGradientEnergy o c + minusGradientEnergy o c)
    hHi (hZi.add hWi) hInv hturn hsym htr hE
  have hv : ∀ᵐ c ∂normalizedVolume g,
      0 ≤ plusNorm o c ∧ plusNorm o c ≤ 2 ∧ σ c ≤ 1 := by
    filter_upwards [] with c
    exact ⟨plusNorm_nonneg o c, by linarith [hsum c, minusNorm_nonneg o c], hσ c⟩
  have hb : ∀ᵐ c ∂normalizedVolume g,
      0 ≤ minusNorm o c ∧ minusNorm o c ≤ 2 ∧ τ c ≤ 1 := by
    filter_upwards [] with c
    exact ⟨minusNorm_nonneg o c, by linarith [hsum c, plusNorm_nonneg o c], hτ c⟩
  have hplus := integrated_gradient_energy_le hv hvi hci hZ
  have hminus := integrated_gradient_energy_le hb hbi hdi hW
  rw [hmean, integral_add hZi hWi, integral_add hvi hbi]
  linarith

end

end PositiveEinsteinFour.Geometry

end OAI
