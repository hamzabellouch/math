import OAI.Geometry.RCD.Coordinates.MatrixNormConversion
import OAI.Geometry.RCD.Coordinates.PositiveForms
import Mathlib.MeasureTheory.VectorMeasure.Order

namespace OAI

/-!
# Positive measure-valued forms on a finite coordinate span

This constructs the real mass operators from a finite family of signed
measures, retaining singular mass. The existence and local Bochner
identification of that family are separate analytic obligations.
-/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

/-- The finite-dimensional restriction of a positive, symmetric,
measure-valued quadratic form, such as the local Bochner measure. -/
structure PositiveBilinearMeasure (X E : Type*) [MeasurableSpace X]
    [AddCommGroup E] [Module ℝ E] where
  bilinear : E →ₗ[ℝ] E →ₗ[ℝ] SignedMeasure X
  symmetric : ∀ v w, bilinear v w = bilinear w v
  nonneg : ∀ v, 0 ≤ bilinear v v

namespace PositiveBilinearMeasure

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (M : PositiveBilinearMeasure X E)

def evaluated (s : Set X) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => M.bilinear v w s)
    (by intro u v w; simp)
    (by intro c v w; simp)
    (by intro u v w; simp)
    (by intro c v w; simp)

def evaluatedContinuous (s : Set X) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap.comp
    (M.evaluated s)).toContinuousLinearMap

def massOperator (s : Set X) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (M.evaluatedContinuous s)

theorem massOperator_inner (s : Set X) (v w : E) :
    ⟪M.massOperator s v, w⟫_ℝ = M.bilinear v w s :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

theorem massOperator_isPositive (s : Set X) (hs : MeasurableSet s) :
    (M.massOperator s).IsPositive := by
  constructor
  · intro v w
    change ⟪M.massOperator s v, w⟫_ℝ = ⟪v, M.massOperator s w⟫_ℝ
    calc
      _ = M.bilinear v w s := M.massOperator_inner s v w
      _ = M.bilinear w v s := congrArg (fun m : SignedMeasure X => m s) (M.symmetric v w)
      _ = ⟪M.massOperator s w, v⟫_ℝ := (M.massOperator_inner s w v).symm
      _ = _ := real_inner_comm _ _
  · intro v
    change 0 ≤ ⟪M.massOperator s v, v⟫_ℝ
    rw [massOperator_inner]
    simpa using M.nonneg v s hs

/-- Every diagonal signed measure is converted to an actual positive
finite measure, rather than replaced by a density with respect to volume. -/
def measure (v : E) : Measure X :=
  (M.bilinear v v).toMeasureOfZeroLE Set.univ MeasurableSet.univ
    (by simpa only [VectorMeasure.le_restrict_univ_iff_le] using M.nonneg v)

instance measure_finite (v : E) : IsFiniteMeasure (M.measure v) :=
  SignedMeasure.toMeasureOfZeroLE_finite _ _ _

theorem measure_real (v : E) (s : Set X) (hs : MeasurableSet s) :
    (M.measure v).real s = ⟪v, M.massOperator s v⟫_ℝ := by
  calc
    _ = M.bilinear v v s := by
      simpa only [measure, Set.univ_inter] using
        SignedMeasure.toMeasureOfZeroLE_real_apply (M.bilinear v v) _ MeasurableSet.univ hs
    _ = ⟪M.massOperator s v, v⟫_ℝ := (M.massOperator_inner s v v).symm
    _ = _ := real_inner_comm _ _

/-- Change of coordinate columns acts on the full signed measures. -/
def comap (A : E →ₗ[ℝ] E) : PositiveBilinearMeasure X E where
  bilinear := M.bilinear.compl₁₂ A A
  symmetric v w := M.symmetric (A v) (A w)
  nonneg v := M.nonneg (A v)

theorem comap_massOperator (A : E →L[ℝ] E) (s : Set X) :
    (M.comap A.toLinearMap).massOperator s =
      A.adjoint.comp ((M.massOperator s).comp A) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [massOperator_inner]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    massOperator_inner]
  rfl

/-- The quadratic triangle bound holds for the full measure on every
measurable set, so singular mass is included. -/
theorem measure_add_le (v w : E) (s : Set X) (hs : MeasurableSet s) :
    (M.measure (v + w)).real s ≤ 2 * ((M.measure v).real s + (M.measure w).real s) := by
  rw [measure_real M _ s hs, measure_real M _ s hs, measure_real M _ s hs]
  have hD := M.massOperator_isPositive s hs
  have hp := hD.inner_nonneg_right (v - w)
  have hsym : ⟪w, M.massOperator s v⟫_ℝ = ⟪v, M.massOperator s w⟫_ℝ := by
    rw [real_inner_comm, hD.inner_left_eq_inner_right]
  simp only [map_sub, inner_sub_left, inner_sub_right, hsym] at hp
  simp only [map_add, inner_add_left, inner_add_right, hsym]
  linarith

/-- Covariance for the actual positive diagonal measures. -/
theorem comap_measure_real (A : E →L[ℝ] E) (v : E) (s : Set X)
    (hs : MeasurableSet s) :
    ((M.comap A.toLinearMap).measure v).real s = (M.measure (A v)).real s := by
  rw [measure_real _ _ s hs, comap_massOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    measure_real _ _ s hs]

section Trace

variable {n : ℕ} (N : PositiveBilinearMeasure X (Euclidean n))

def traceMass (s : Set X) : ℝ :=
  ∑ i : Fin n, (N.measure (EuclideanSpace.single i 1)).real s

theorem traceMass_nonneg (s : Set X) : 0 ≤ N.traceMass s :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- Positivity bounds every matrix entry by its trace. -/
theorem mass_entry_le_trace (s : Set X) (hs : MeasurableSet s) (i j : Fin n) :
    |N.massOperator s (EuclideanSpace.single j 1) i| ≤ N.traceMass s := by
  let ei : Euclidean n := EuclideanSpace.single i 1
  let ej : Euclidean n := EuclideanSpace.single j 1
  let D := N.massOperator s
  have hD := N.massOperator_isPositive s hs
  have hii : ⟪ei, D ei⟫_ℝ ≤ N.traceMass s := by
    rw [← N.measure_real ei s hs]
    change (N.measure (EuclideanSpace.single i 1)).real s ≤
      ∑ j : Fin n, (N.measure (EuclideanSpace.single j 1)).real s
    exact Finset.single_le_sum
      (f := fun k : Fin n => (N.measure (EuclideanSpace.single k 1)).real s)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
  have hjj : ⟪ej, D ej⟫_ℝ ≤ N.traceMass s := by
    rw [← N.measure_real ej s hs]
    change (N.measure (EuclideanSpace.single j 1)).real s ≤
      ∑ i : Fin n, (N.measure (EuclideanSpace.single i 1)).real s
    exact Finset.single_le_sum
      (f := fun k : Fin n => (N.measure (EuclideanSpace.single k 1)).real s)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have hp := positive_form_cauchy_schwarz hD ei ej
  have habs : |⟪ei, D ej⟫_ℝ| ≤ (⟪ei, D ei⟫_ℝ + ⟪ej, D ej⟫_ℝ) / 2 := by
    have hsum := add_nonneg (hD.inner_nonneg_right ei) (hD.inner_nonneg_right ej)
    nlinarith [sq_abs ⟪ei, D ej⟫_ℝ, sq_nonneg (⟪ei, D ei⟫_ℝ - ⟪ej, D ej⟫_ℝ),
      abs_nonneg ⟪ei, D ej⟫_ℝ]
  have he := habs.trans (by linarith :
    (⟪ei, D ei⟫_ℝ + ⟪ej, D ej⟫_ℝ) / 2 ≤ N.traceMass s)
  simpa only [ei, ej, D, EuclideanSpace.inner_single_left, conj_trivial, one_mul] using he

theorem massOperator_norm_le_trace (s : Set X) (hs : MeasurableSet s) :
    ‖N.massOperator s‖ ≤ (n : ℝ) ^ 2 * N.traceMass s :=
  euclidean_operator_norm_le_of_entries _ (N.traceMass_nonneg s) (N.mass_entry_le_trace s hs)

end Trace

end PositiveBilinearMeasure

end RegularPointCoordinates

end

end OAI
