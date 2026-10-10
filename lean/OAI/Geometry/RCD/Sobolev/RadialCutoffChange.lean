import OAI.Geometry.RCD.Harmonic.CenteredProjectionRows

namespace OAI

/-! # Changing the local constant in a radial Sobolev residual -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Two cutoff extensions of one produce the same local value and energy
of the centered radial residual. -/
theorem centered_radial_cutoff_change {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g eta chi : SobolevSpace μ hQ)
    (z b : Euclidean n) (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hchi : SobolevSpace.toLp μ hQ chi =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) :
    let f := g - centeredAffineSobolev μ hQ u eta z b
    let f' := g - centeredAffineSobolev μ hQ u chi z b
    (SobolevSpace.restrictLp μ hQ Ω f = SobolevSpace.restrictLp μ hQ Ω f') ∧
      (∫ x in Ω, localGamma μ hQ f f x ∂μ) = ∫ x in Ω, localGamma μ hQ f' f' x ∂μ := by
  dsimp only
  have heq : SobolevSpace.restrictLp μ hQ Ω (g - centeredAffineSobolev μ hQ u eta z b) =
      SobolevSpace.restrictLp μ hQ Ω (g - centeredAffineSobolev μ hQ u chi z b) := by
    rw [map_sub, map_sub, centered_affine_restrict_cutoff_eq μ hQ u z b Ω hfin eta chi heta hchi]
  refine ⟨heq, ?_⟩
  have hrep : SobolevSpace.toLp μ hQ (g - centeredAffineSobolev μ hQ u eta z b) =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ (g - centeredAffineSobolev μ hQ u chi z b) := by
    filter_upwards [SobolevSpace.restrictLp_coe μ hQ Ω (g - centeredAffineSobolev μ hQ u eta z b),
      SobolevSpace.restrictLp_coe μ hQ Ω (g - centeredAffineSobolev μ hQ u chi z b)] with x hx hy
    exact hx.symm.trans ((congrArg (fun h : Lp ℝ 2 (μ.restrict Ω) => h x) heq).trans hy)
  exact integral_congr_ae (localGamma_pair_congr_ae μ hQ hrep hrep)

end RegularPointCoordinates

end

end OAI
