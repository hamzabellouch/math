import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightMeasurability
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitTests

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem continuous_rotationIterate_joint (k : ℤ) :
    Continuous (fun p : (ℕ → ℝ) × Base => rotationIterate p.1 k p.2) := by
  unfold rotationIterate
  fun_prop

theorem measurable_rotationIterate_joint (k : ℤ) :
    Measurable (fun p : (ℕ → ℝ) × Base => rotationIterate p.1 k p.2) :=
  (continuous_rotationIterate_joint k).measurable

namespace SamplingWeights

theorem measurable_orbitWeight_inverse_joint (D I : Finset ℕ) (h α : ℝ) (n : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × Base =>
      orbitWeight D I h α p.1 n (rotationIterate p.1 (-(n : ℤ)) p.2)) := by
  have hp : Measurable (fun p : (ℕ → ℝ) × Base =>
      (p.1, rotationIterate p.1 (-(n : ℤ)) p.2)) :=
    (measurable_fst : Measurable (Prod.fst : (ℕ → ℝ) × Base → (ℕ → ℝ))).prodMk
      (measurable_rotationIterate_joint (-(n : ℤ)))
  simpa only [Function.comp_def] using (measurable_orbitWeight_pair D I h α n).comp hp

theorem measurable_orbitTestWeight_joint (D I : Finset ℕ) (h α : ℝ)
    (n : ℕ) (A : Set EndpointPair) (hA : MeasurableSet A) :
    Measurable (fun p : (ℕ → ℝ) × Base => TailTrimming.orbitTestWeight p.1 A
      (orbitWeight D I h α p.1) n p.2) := by
  have hp : Measurable (fun p : (ℕ → ℝ) × Base =>
      (p.2, rotationIterate p.1 (n : ℤ) p.2)) :=
    measurable_snd.prodMk (measurable_rotationIterate_joint (n : ℤ))
  exact (measurable_orbitWeight_pair D I h α n).indicator (hp hA)

theorem measurable_orbitTestWeight_inverse_joint (D I : Finset ℕ) (h α : ℝ)
    (n : ℕ) (A : Set EndpointPair) (hA : MeasurableSet A) :
    Measurable (fun p : (ℕ → ℝ) × Base => TailTrimming.orbitTestWeight p.1 A
      (orbitWeight D I h α p.1) n (rotationIterate p.1 (-(n : ℤ)) p.2)) := by
  have hp : Measurable (fun p : (ℕ → ℝ) × Base =>
      (p.1, rotationIterate p.1 (-(n : ℤ)) p.2)) :=
    (measurable_fst : Measurable (Prod.fst : (ℕ → ℝ) × Base → (ℕ → ℝ))).prodMk
      (measurable_rotationIterate_joint (-(n : ℤ)))
  simpa only [Function.comp_def] using (measurable_orbitTestWeight_joint D I h α n A hA).comp hp

theorem measurable_firstTestAverage_joint (D I N : Finset ℕ) (h α : ℝ)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    Measurable (fun p : (ℕ → ℝ) × Base => (N.card : ℝ)⁻¹ *
      ∑ n ∈ N, TailTrimming.orbitTestWeight p.1 A
        (orbitWeight D I h α p.1) n p.2) := by
  exact measurable_const.mul (Finset.measurable_sum N
    (fun n _ => measurable_orbitTestWeight_joint D I h α n A hA))

theorem measurable_secondTestAverage_joint (D I N : Finset ℕ) (h α : ℝ)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    Measurable (fun p : (ℕ → ℝ) × Base => (N.card : ℝ)⁻¹ *
      ∑ n ∈ N, TailTrimming.orbitTestWeight p.1 A
        (orbitWeight D I h α p.1) n (rotationIterate p.1 (-(n : ℤ)) p.2)) := by
  exact measurable_const.mul (Finset.measurable_sum N
    (fun n _ => measurable_orbitTestWeight_inverse_joint D I h α n A hA))

theorem measurable_spatialSquaredError
    (F : (ℕ → ℝ) × Base → ℝ) (hF : Measurable F)
    (z : Base → ℝ) (hz : Measurable z) :
    Measurable (fun θ : ℕ → ℝ =>
      ∫⁻ x, ENNReal.ofReal ((F (θ, x) - z x)^2) ∂baseMeasure) := by
  exact (((hF.sub (hz.comp measurable_snd)).pow_const 2).ennreal_ofReal).lintegral_prod_right

end SamplingWeights
end Invariant233.ProductModel

end

end OAI
