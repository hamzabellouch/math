import OAI.Geometry.RCD.Sobolev.HessianCommutatorEnergy

namespace OAI

/-! # Independence of the chosen Sobolev gradient representatives -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The commutator estimate applies to the representatives selected by
radial approximation, even when the Hessian construction chose others. -/
theorem commutator_error_transfer {Ω : Set X}
    (f v u g₀ h₀ g h : SobolevSpace μ hQ)
    (hg₀ : SobolevSpace.toLp μ hQ g₀ =ᵐ[μ.restrict Ω] localGamma μ hQ f u)
    (hh₀ : SobolevSpace.toLp μ hQ h₀ =ᵐ[μ.restrict Ω] localGamma μ hQ v u)
    (hg : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict Ω] localGamma μ hQ f u)
    (hh : SobolevSpace.toLp μ hQ h =ᵐ[μ.restrict Ω] localGamma μ hQ v u)
    {D : ℝ}
    (herror : (∫ x in Ω, (localGamma μ hQ v g₀ x - localGamma μ hQ f h₀ x -
      localGamma μ hQ v u x) ^ 2 ∂μ) ≤ D) :
    (∫ x in Ω, (localGamma μ hQ v g x - localGamma μ hQ f h x -
      localGamma μ hQ v u x) ^ 2 ∂μ) ≤ D := by
  have hvg := localGamma_pair_congr_ae μ hQ (f := v) (f' := v)
    Filter.EventuallyEq.rfl (hg.trans hg₀.symm)
  have hfh := localGamma_pair_congr_ae μ hQ (f := f) (f' := f)
    Filter.EventuallyEq.rfl (hh.trans hh₀.symm)
  have heq : (fun x => (localGamma μ hQ v g x - localGamma μ hQ f h x -
      localGamma μ hQ v u x) ^ 2) =ᵐ[μ.restrict Ω]
      fun x => (localGamma μ hQ v g₀ x - localGamma μ hQ f h₀ x -
        localGamma μ hQ v u x) ^ 2 := by
    filter_upwards [hvg, hfh] with x hx hy
    rw [hx, hy]
  rwa [integral_congr_ae heq]

end RegularPointCoordinates

end

end OAI
