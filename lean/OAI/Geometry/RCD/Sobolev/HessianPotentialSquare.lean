import OAI.Geometry.RCD.Sobolev.HessianPotentialProduct

namespace OAI

/-! # Hessians of the quadratic perturbations used in Bochner -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The quadratic perturbation has the expected rank-one second derivative. -/
theorem localHessianAction_potential_square {Ω : Set X}
    (g u v gu gv uv : SobolevSpace μ hQ) (B E F : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤B)
    (hguB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ gu x|≤E)
    (hgvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ gv x|≤F)
    (hgu : SobolevSpace.toLp μ hQ gu =ᵐ[μ.restrict Ω] localGamma μ hQ g u)
    (hgv : SobolevSpace.toLp μ hQ gv =ᵐ[μ.restrict Ω] localGamma μ hQ g v) :
    localHessianAction μ hQ (SobolevSpace.product μ hQ g g B B) u v
      ((2 : ℝ) • SobolevSpace.product μ hQ g gu B E)
      ((2 : ℝ) • SobolevSpace.product μ hQ g gv B F) uv =ᵐ[μ.restrict Ω] fun x =>
      2*SobolevSpace.toLp μ hQ g x*localHessianAction μ hQ g u v gu gv uv x+
        2*localGamma μ hQ g u x*localGamma μ hQ g v x := by
  have h := localHessianAction_potential_product μ hQ g g u v gu gv gu gv uv
    B B E F E F hg hg hguB hgvB hguB hgvB hgu hgv hgu hgv
  dsimp only at h
  rw [← two_smul ℝ (SobolevSpace.product μ hQ g gu B E),
    ← two_smul ℝ (SobolevSpace.product μ hQ g gv B F)] at h
  exact h.mono fun x hx => by rw [hx]; ring

end RegularPointCoordinates

end

end OAI
