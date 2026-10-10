import OAI.Geometry.RCD.Sobolev.CompactMeasureLaplacian

namespace OAI

/-!
# Energy product identity for compact measure-source constructions

The actual bounded Sobolev product satisfies the integration-by-parts
identity needed to multiply a local measure Laplacian by a cutoff.
-/

open Set MeasureTheory
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
private theorem bounded_gamma_integrable (f g h : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    Integrable (fun x => SobolevSpace.toLp μ hQ f x * localGamma μ hQ g h x) μ := by
  apply (localGamma_memL1 μ hQ g h).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ f))
  simpa only [Real.norm_eq_abs] using hf

/-- Integrating the genuine carré-du-champ product rule. -/
theorem energy_bounded_product (f g h : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    energyForm μ hQ (SobolevSpace.product μ hQ f g C D) h =
      (∫ x, SobolevSpace.toLp μ hQ f x * localGamma μ hQ g h x ∂μ) +
      (∫ x, SobolevSpace.toLp μ hQ g x * localGamma μ hQ f h x ∂μ) := by
  rw [← integral_localGamma_eq_energyForm]
  rw [integral_congr_ae (localGamma_product_left μ hQ f g h C D hf hg)]
  exact integral_add (bounded_gamma_integrable μ hQ f g h C hf)
    (bounded_gamma_integrable μ hQ g f h D hg)

omit [ProperSpace X] in
private theorem gamma_weight_comm (f g h : SobolevSpace μ hQ) :
    (∫ x, SobolevSpace.toLp μ hQ f x * localGamma μ hQ g h x ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ f x * localGamma μ hQ h g x ∂μ :=
  integral_congr_ae ((localGamma_comm μ hQ g h).mono fun _ hx => congrArg (_ * ·) hx)

/-- The two cross terms needed for the full signed cutoff source. -/
theorem energy_product_integration_by_parts (f g h : SobolevSpace μ hQ) (C D H : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x| ≤ H) :
    energyForm μ hQ (SobolevSpace.product μ hQ f g C D) h =
      energyForm μ hQ f (SobolevSpace.product μ hQ g h D H) +
      energyForm μ hQ g (SobolevSpace.product μ hQ f h C H) -
      2 * ∫ x, SobolevSpace.toLp μ hQ h x * localGamma μ hQ f g x ∂μ := by
  rw [energy_bounded_product μ hQ f g h C D hf hg,
    energyForm_comm μ hQ f, energy_bounded_product μ hQ g h f D H hg hh,
    energyForm_comm μ hQ g, energy_bounded_product μ hQ f h g C H hf hh]
  rw [gamma_weight_comm μ hQ g h f, gamma_weight_comm μ hQ f h g,
    gamma_weight_comm μ hQ h g f]
  ring

end RegularPointCoordinates

end

end OAI
