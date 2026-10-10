import OAI.MeasureTheory.Falconer.Estimates.WeightedLowpass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Fourier transform of the original masked pair law

The pair measure is unchanged; the distance weight and every old descriptor
mask stay inside its integral. This is the input to stationary inversion.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem descriptorPairWeight_nonneg (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (z : Space d × Space d) :
    0 ≤ descriptorPairWeight w₀ Q ρ m N σ J i a B S z := by
  exact mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (mul_nonneg dist_nonneg (by positivity)) _)
    (descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover _ _).1)
    (descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover _ _).1

theorem integral_maskedCellDistance (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube d) (F : ℝ → ℂ)
    (hF : AEStronglyMeasurable F (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)) :
    (∫ s, F s ∂maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) =
      ∫ z, ((profileModelMass m N a)⁻¹^2 *
        descriptorPairWeight w₀ Q ρ m N σ J i a B S z) • F (dist z.1 z.2)
        ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [maskedCellDistance,integral_map (by fun_prop) hF]
  have hw : Measurable (fun z : Space d × Space d => ENNReal.ofReal
      ((profileModelMass m N a)⁻¹^2 * descriptorPairWeight w₀ Q ρ m N σ J i a B S z)) :=
    (measurable_const.mul (descriptorPairWeight_measurable w₀ Q ρ m N σ J i a B S)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
    (descriptorPairWeight_nonneg w₀ Q ρ m N σ J i a B S hcover z))]

theorem maskedCellDistance_fourier (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (X Y : DyadicCube d) (r : ℝ) :
    charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r =
      ∫ z, (((profileModelMass m N a)⁻¹^2 *
        descriptorPairWeight w₀ Q ρ m N σ J i a B S z : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((r * dist z.1 z.2 : ℝ) : ℂ))
        ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier) := by
  rw [charFun_apply_real,integral_maskedCellDistance w₀ Q ρ m N σ J i a B S hcover]
  · apply integral_congr_ae
    filter_upwards with z
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring_nf
  · fun_prop

end Falconer

end OAI
