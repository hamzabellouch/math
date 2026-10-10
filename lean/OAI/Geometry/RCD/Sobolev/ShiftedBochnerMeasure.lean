import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace OAI

/-!
# The full shifted Bochner measure

The trace inequality for the Hessian gives the displayed scalar lower
bound. The associated positive quadratic measure is defined on pairs
`(function direction, scalar shift)`. In particular, the quadratic
triangle inequality applies to two different Poisson replacements and
retains all singular mass.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scalar consequence of `M >= |Hess f|² m` and `tr Hess f = Δf`
needed to subtract a constant multiple of the metric. -/
def ShiftedBochnerLowerBound (M : PositiveBilinearMeasure X E)
    (ν : Measure X) (ell : E →ₗ[ℝ] ℝ) (n : ℝ) : Prop :=
  ∀ (v : E) (b : ℝ) (s : Set X), MeasurableSet s →
    (2 * b * ell v - n * b ^ 2) * ν.real s ≤ (M.measure v).real s

/-- Subtracting the trace correction from the full Bochner measure makes
a positive bilinear measure on the augmented space. -/
def shiftedBochnerMeasure (M : PositiveBilinearMeasure X E)
    (ν : Measure X) [IsFiniteMeasure ν] (ell : E →ₗ[ℝ] ℝ) (n : ℝ)
    (h : ShiftedBochnerLowerBound M ν ell n) : PositiveBilinearMeasure X (WithLp 2 (E × ℝ)) where
  bilinear := LinearMap.mk₂ ℝ
    (fun v w => M.bilinear v.fst w.fst -
      (v.snd * ell w.fst + w.snd * ell v.fst - n * v.snd * w.snd) • ν.toSignedMeasure)
    (by
      intro u v w
      simp only [WithLp.add_fst, WithLp.add_snd, map_add, LinearMap.add_apply]
      module)
    (by
      intro c v w
      simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      module)
    (by
      intro u v w
      simp only [WithLp.add_fst, WithLp.add_snd, map_add]
      module)
    (by
      intro c v w
      simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, smul_eq_mul]
      module)
  symmetric v w := by
    change M.bilinear v.fst w.fst -
      (v.snd * ell w.fst + w.snd * ell v.fst - n * v.snd * w.snd) • ν.toSignedMeasure =
      M.bilinear w.fst v.fst -
      (w.snd * ell v.fst + v.snd * ell w.fst - n * w.snd * v.snd) • ν.toSignedMeasure
    rw [M.symmetric]
    congr 2
    ring
  nonneg v := by
    intro s hs
    change 0 ≤ (M.bilinear v.fst v.fst -
      (v.snd * ell v.fst + v.snd * ell v.fst - n * v.snd * v.snd) • ν.toSignedMeasure) s
    rw [sub_apply, smul_apply, Measure.toSignedMeasure_apply_measurable hs]
    have hb := h v.fst v.snd s hs
    rw [M.measure_real _ s hs, real_inner_comm, M.massOperator_inner] at hb
    simp only [smul_eq_mul]
    nlinarith

namespace ShiftedBochnerMeasure

variable (M : PositiveBilinearMeasure X E) (ν : Measure X) [IsFiniteMeasure ν]
  (ell : E →ₗ[ℝ] ℝ) (n : ℝ) (h : ShiftedBochnerLowerBound M ν ell n)

theorem diagonal (v : E) (b : ℝ) :
    (shiftedBochnerMeasure M ν ell n h).bilinear (WithLp.toLp 2 (v, b)) (WithLp.toLp 2 (v, b)) =
      M.bilinear v v - (2 * b * ell v - n * b ^ 2) • ν.toSignedMeasure := by
  change M.bilinear v v - (b * ell v + b * ell v - n * b * b) • ν.toSignedMeasure = _
  congr 2
  ring

/-- The zero shift recovers the original measure, not just its density. -/
theorem zero_shift (v : E) :
    (shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (v, (0 : ℝ))) = M.measure v := by
  change (M.bilinear v v - (0 * ell v + 0 * ell v - n * 0 * 0) • ν.toSignedMeasure).toMeasureOfZeroLE
    univ MeasurableSet.univ _ = _
  simp [PositiveBilinearMeasure.measure]

theorem mass (v : E) (b : ℝ) (s : Set X) (hs : MeasurableSet s) :
    ((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (v, b))).real s =
      (M.measure v).real s - (2 * b * ell v - n * b ^ 2) * ν.real s := by
  rw [PositiveBilinearMeasure.measure_real _ _ s hs, real_inner_comm,
    PositiveBilinearMeasure.massOperator_inner, diagonal,
    sub_apply, smul_apply, Measure.toSignedMeasure_apply_measurable hs,
    M.measure_real _ s hs, real_inner_comm, M.massOperator_inner]
  rfl

/-- The full-measure triangle estimate for two Poisson functions and two
scalar metric shifts. -/
theorem difference_mass_le (v w : E) (b c : ℝ) (s : Set X) (hs : MeasurableSet s) :
    ((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (v - w, b - c))).real s ≤
      2 * (((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (v, b))).real s +
        ((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (w, c))).real s) := by
  have hb := (shiftedBochnerMeasure M ν ell n h).measure_add_le (WithLp.toLp 2 (v, b)) (WithLp.toLp 2 (-w, -c)) s hs
  have he : ((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (-w, -c))).real s =
      ((shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (w, c))).real s := by
    rw [mass M ν ell n h _ _ s hs, mass M ν ell n h _ _ s hs,
      M.measure_real _ s hs, M.measure_real _ s hs]
    simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg]
    ring
  simpa only [← WithLp.toLp_add, Prod.mk_add_mk, ← sub_eq_add_neg, he] using hb

section Integration

variable [TopologicalSpace X] [BorelSpace X]

/-- Bounded tests integrate the full shifted measure. -/
theorem integral (v : E) (b : ℝ) (χ : X →ᵇ ℝ) :
    (∫ x, χ x ∂(shiftedBochnerMeasure M ν ell n h).measure (WithLp.toLp 2 (v, b))) =
      (∫ x, χ x ∂M.measure v) - (2 * b * ell v - n * b ^ 2) * ∫ x, χ x ∂ν := by
  rw [← VectorMeasure.integral_toSignedMeasure,
    PositiveBilinearMeasure.measure_toSignedMeasure, diagonal,
    VectorMeasure.integral_sub_vectorMeasure
      (PositiveBilinearMeasure.integrable_weight χ _)
      (PositiveBilinearMeasure.integrable_weight χ _),
    VectorMeasure.integral_smul_vectorMeasure, ← M.measure_toSignedMeasure v,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  rfl

end Integration
end ShiftedBochnerMeasure
end RegularPointCoordinates

end

end OAI
