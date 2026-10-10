import OAI.Geometry.RCD.Coordinates.PositiveBilinearMeasure
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

/-!
# Integrating full positive measure-valued forms

Bounded continuous weights act on the full signed measures. In particular,
their singular parts contribute to every weighted quadratic form. These
constructions do not assert existence of the local Bochner measure.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates
namespace PositiveBilinearMeasure

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (M : PositiveBilinearMeasure X E)

theorem integrable_weight (w : X →ᵇ ℝ) (ν : SignedMeasure X) :
    ν.Integrable w := by
  let : IsFiniteMeasure ν.variation := by
    rw [← ν.totalVariation_eq_variation]
    infer_instance
  exact Integrable.of_bound w.continuous.aestronglyMeasurable ‖w‖
    (Filter.Eventually.of_forall w.norm_coe_le_norm)

/-- Integration is bilinear in the coordinate directions, including the
off-diagonal signed measures. -/
def weightedBilinear (w : X →ᵇ ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v z => ∫ᵛ x, w x ∂<•(M.bilinear v z))
    (by
      intro u v z
      rw [map_add, LinearMap.add_apply]
      exact VectorMeasure.integral_add_vectorMeasure
        (integrable_weight w _) (integrable_weight w _))
    (by intro c v z; simp)
    (by
      intro u v z
      rw [map_add]
      exact VectorMeasure.integral_add_vectorMeasure
        (integrable_weight w _) (integrable_weight w _))
    (by intro c v z; simp)

def weightedContinuous (w : X →ᵇ ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap.comp
    (M.weightedBilinear w)).toContinuousLinearMap

def weightedOperator (w : X →ᵇ ℝ) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (M.weightedContinuous w)

theorem weightedOperator_inner (w : X →ᵇ ℝ) (v z : E) :
    ⟪M.weightedOperator w v, z⟫_ℝ = ∫ᵛ x, w x ∂<•(M.bilinear v z) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

omit [TopologicalSpace X] [BorelSpace X] [FiniteDimensional ℝ E] in
theorem measure_toSignedMeasure (v : E) :
    (M.measure v).toSignedMeasure = M.bilinear v v :=
  SignedMeasure.toMeasureOfZeroLE_toSignedMeasure _ _

/-- Diagonal weighted forms are ordinary integrals against the actual
positive measure, without discarding singular mass. -/
theorem weightedOperator_energy (w : X →ᵇ ℝ) (v : E) :
    ⟪v, M.weightedOperator w v⟫_ℝ = ∫ x, w x ∂(M.measure v) := by
  rw [real_inner_comm, weightedOperator_inner, ← M.measure_toSignedMeasure v]
  exact VectorMeasure.integral_toSignedMeasure

/-- A real weighted measure-valued form stays symmetric even when the
weight changes sign. -/
theorem weightedOperator_isSymmetric (w : X →ᵇ ℝ) :
    (M.weightedOperator w).IsSymmetric := by
  intro v z
  change ⟪M.weightedOperator w v, z⟫_ℝ = ⟪v, M.weightedOperator w z⟫_ℝ
  calc
    _ = ∫ᵛ x, w x ∂<•(M.bilinear v z) := M.weightedOperator_inner w v z
    _ = ∫ᵛ x, w x ∂<•(M.bilinear z v) := by rw [M.symmetric v z]
    _ = ⟪M.weightedOperator w z, v⟫_ℝ := (M.weightedOperator_inner w z v).symm
    _ = _ := real_inner_comm _ _

theorem weightedOperator_isPositive (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) :
    (M.weightedOperator w).IsPositive := by
  constructor
  · intro v z
    change ⟪M.weightedOperator w v, z⟫_ℝ = ⟪v, M.weightedOperator w z⟫_ℝ
    calc
      _ = ∫ᵛ x, w x ∂<•(M.bilinear v z) := M.weightedOperator_inner w v z
      _ = ∫ᵛ x, w x ∂<•(M.bilinear z v) := by rw [M.symmetric v z]
      _ = ⟪M.weightedOperator w z, v⟫_ℝ := (M.weightedOperator_inner w z v).symm
      _ = _ := real_inner_comm _ _
  · intro v
    change 0 ≤ ⟪M.weightedOperator w v, v⟫_ℝ
    rw [real_inner_comm, weightedOperator_energy]
    exact integral_nonneg hw

/-- A change of coordinates commutes with integration of full measures. -/
theorem comap_weightedOperator (A : E →L[ℝ] E) (w : X →ᵇ ℝ) :
    (M.comap A.toLinearMap).weightedOperator w =
      A.adjoint.comp ((M.weightedOperator w).comp A) := by
  ext v
  apply ext_inner_right ℝ
  intro z
  rw [weightedOperator_inner]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    weightedOperator_inner]
  rfl

theorem weightedOperator_energy_mono (w z : X →ᵇ ℝ) (hwz : ∀ x, w x ≤ z x)
    (v : E) : ⟪v, M.weightedOperator w v⟫_ℝ ≤ ⟪v, M.weightedOperator z v⟫_ℝ := by
  rw [weightedOperator_energy, weightedOperator_energy]
  apply integral_mono
  · exact Integrable.of_bound w.continuous.aestronglyMeasurable ‖w‖
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  · exact Integrable.of_bound z.continuous.aestronglyMeasurable ‖z‖
      (Filter.Eventually.of_forall z.norm_coe_le_norm)
  · exact hwz

/-- A kernel lower bound controls the mass of every measurable testing
set, including the singular part of the measure. -/
theorem massOperator_le_weightedOperator (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x)
    (s : Set X) (hs : MeasurableSet s) (c : ℝ) (hc : ∀ x ∈ s, c ≤ w x) (v : E) :
    c * ⟪v, M.massOperator s v⟫_ℝ ≤ ⟪v, M.weightedOperator w v⟫_ℝ := by
  rw [weightedOperator_energy, ← M.measure_real v s hs]
  have hi : Integrable w (M.measure v) :=
    Integrable.of_bound w.continuous.aestronglyMeasurable ‖w‖
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  calc
    _ = ∫ x in s, c ∂(M.measure v) := by simp [mul_comm]
    _ ≤ ∫ x in s, w x ∂(M.measure v) :=
      setIntegral_mono_on (integrable_const c) hi.integrableOn hs hc
    _ ≤ ∫ x, w x ∂(M.measure v) :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall hw)

/-- A supported, bounded weight is bounded by the full mass on its support. -/
theorem weightedOperator_le_massOperator (w : X →ᵇ ℝ) (s : Set X)
    (hs : MeasurableSet s) (hws : ∀ x ∉ s, w x = 0) (C : ℝ)
    (hC : ∀ x ∈ s, w x ≤ C) (v : E) :
    ⟪v, M.weightedOperator w v⟫_ℝ ≤ C * ⟪v, M.massOperator s v⟫_ℝ := by
  rw [weightedOperator_energy, ← M.measure_real v s hs]
  have hi : Integrable w (M.measure v) :=
    Integrable.of_bound w.continuous.aestronglyMeasurable ‖w‖
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  calc
    _ = ∫ x in s, w x ∂(M.measure v) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hws).symm
    _ ≤ ∫ x in s, C ∂(M.measure v) :=
      setIntegral_mono_on hi.integrableOn (integrable_const C) hs hC
    _ = _ := by simp [mul_comm]

/-- A pointwise kernel-difference bound transfers to the full mass measure,
without assuming that the measure has a density. -/
theorem weightedOperator_energy_difference_le (w z B : X →ᵇ ℝ)
    (hB : ∀ x, |w x - z x| ≤ B x) (v : E) :
    |⟪v, (M.weightedOperator w - M.weightedOperator z) v⟫_ℝ| ≤
      ⟪v, M.weightedOperator B v⟫_ℝ := by
  have hi (f : X →ᵇ ℝ) : Integrable f (M.measure v) :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  rw [sub_apply, inner_sub_right, weightedOperator_energy, weightedOperator_energy,
    weightedOperator_energy, ← integral_sub (hi w) (hi z)]
  calc
    _ ≤ ∫ x, |w x - z x| ∂(M.measure v) := abs_integral_le_integral_abs
    _ ≤ ∫ x, B x ∂(M.measure v) := integral_mono ((hi w).sub (hi z)).abs (hi B) hB

end PositiveBilinearMeasure
end RegularPointCoordinates

end

end OAI
