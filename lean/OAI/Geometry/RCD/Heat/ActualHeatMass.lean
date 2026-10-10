import OAI.Geometry.RCD.Heat.ActualHeatGrams
import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure

namespace OAI

/-!
# Heat averages of full local mass measures

The weight is the same actual heat kernel and compact cutoff used in the
Gram matrices. The mass can have a singular part and is identified locally
with the Bochner measure.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

/-- The actual cutoff heat weight, as a bounded continuous function. -/
def cutoffHeatWeight {t : ℝ} (ht : 0 < t) (x : X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => χ y * p t x y) (hχ.mul (hp.continuous_right t ht x))
    (cutoffHeatWeightBound μ hQ hp hχ hsχ ht x)
    (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x)

theorem cutoffHeatWeight_apply {t : ℝ} (ht : 0 < t) (x y : X) :
    cutoffHeatWeight μ hQ hp hχ hsχ ht x y = χ y * p t x y := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (M : PositiveBilinearMeasure X E)

/-- Heat integration of the full mass measure on a finite coordinate span. -/
def cutoffHeatMass {t : ℝ} (ht : 0 < t) (x : X) : E →L[ℝ] E :=
  M.weightedOperator (cutoffHeatWeight μ hQ hp hχ hsχ ht x)

theorem cutoffHeatMass_energy {t : ℝ} (ht : 0 < t) (x : X) (v : E) :
    ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht x v⟫_ℝ =
      ∫ y, (χ y * p t x y) ∂(M.measure v) :=
  M.weightedOperator_energy _ v

theorem cutoffHeatMass_isPositive (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) :
    (cutoffHeatMass μ hQ hp hχ hsχ M ht x).IsPositive :=
  M.weightedOperator_isPositive _ fun y =>
    mul_nonneg (hχpos y) (hp.nonneg t ht x y)

theorem cutoffHeatMass_comap (A : E →L[ℝ] E) {t : ℝ} (ht : 0 < t) (x : X) :
    cutoffHeatMass μ hQ hp hχ hsχ (M.comap A.toLinearMap) ht x =
      A.adjoint.comp ((cutoffHeatMass μ hQ hp hχ hsχ M ht x).comp A) :=
  M.comap_weightedOperator A _

/-- Kernel lower estimates turn directly into estimates for singular or
absolutely continuous mass on the testing ball. -/
theorem cutoffHeatMass_lower_mass (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) (s : Set X) (hs : MeasurableSet s)
    (hχone : ∀ y ∈ s, χ y = 1) (c : ℝ) (hc : ∀ y ∈ s, c ≤ p t x y) (v : E) :
    c * ⟪v, M.massOperator s v⟫_ℝ ≤
      ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht x v⟫_ℝ := by
  apply M.massOperator_le_weightedOperator _
    (fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y)) s hs c
  intro y hy
  change c ≤ χ y * p t x y
  simpa only [hχone y hy, one_mul] using hc y hy

/-- Spatial comparisons of the kernel also compare heat mass matrices,
without needing pointwise representatives of a mass density. -/
theorem cutoffHeatMass_energy_mono (hχpos : ∀ y, 0 ≤ χ y)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x z : X)
    (hkernel : ∀ y, p t x y ≤ p s z y) (v : E) :
    ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht x v⟫_ℝ ≤
      ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M hs z v⟫_ℝ := by
  apply M.weightedOperator_energy_mono
  intro y
  exact mul_le_mul_of_nonneg_left (hkernel y) (hχpos y)

end RegularPointCoordinates

end

end OAI
