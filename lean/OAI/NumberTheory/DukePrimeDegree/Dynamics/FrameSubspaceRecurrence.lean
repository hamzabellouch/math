import OAI.NumberTheory.DukePrimeDegree.Geometry.FullFrameMinors

namespace OAI

/-!
# Diagonal recurrence from transport of an actual subspace

The measurable frame theorem needs only transport of its column space.
The change-of-basis matrix and its nonzero determinant are derived here
from that transport and independence; they are not additional dynamical
hypotheses.
-/

noncomputable section
open MeasureTheory Filter Matrix Set

namespace DukePrimeDegree

theorem ae_frame_diagonal_invariant_of_span_transport
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (hfull : ∀ᵐ x ∂μ, LinearIndependent ℝ (B x).col)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (htransport : ∀ᵐ x ∂μ,
      Submodule.span ℝ (Set.range (B (T x)).col) =
        Submodule.span ℝ (Set.range (Matrix.diagonal a * B x).col)) :
    ∀ᵐ x ∂μ, ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Matrix.diagonal a * B x = B x * C := by
  classical
  have hchanges : ∀ᵐ x ∂μ, ∃ R : Matrix (Fin k) (Fin k) ℝ,
      R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R := by
    filter_upwards [hT.quasiMeasurePreserving.ae hfull, htransport] with x hx ht
    exact exists_invertible_frame_change (Matrix.diagonal a * B x) (B (T x)) hx ht.le
  let R : Y → Matrix (Fin k) (Fin k) ℝ := fun x =>
    if h : ∃ R : Matrix (Fin k) (Fin k) ℝ,
        R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R then
      Classical.choose h else 1
  have hR : ∀ᵐ x ∂μ, (R x).det ≠ 0 := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).1
  have hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).2
  have hpivot : ∀ᵐ x ∂μ, ∃ p : Fin k ↪ Fin n, frameMinor (B x) p ≠ 0 := by
    filter_upwards [hfull] with x hx
    exact exists_nonzero_frameMinor_of_linearIndependent (B x) hx
  exact ae_frame_diagonal_invariant μ T hT B hB hpivot a ha R hR hcov

/-- A fixed-rank frame may be extended by zero outside its invariant rank
event. The projective recurrence then applies to the whole probability
space; restriction to an invariant subspace of the measure is unnecessary. -/
theorem ae_frame_diagonal_invariant_on_event
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, T x ∈ E ↔ x ∈ E)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (hfull : ∀ᵐ x ∂μ, x ∈ E → LinearIndependent ℝ (B x).col)
    (hzero : ∀ᵐ x ∂μ, x ∉ E → B x = 0)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (htransport : ∀ᵐ x ∂μ, x ∈ E →
      Submodule.span ℝ (Set.range (B (T x)).col) =
        Submodule.span ℝ (Set.range (Matrix.diagonal a * B x).col)) :
    ∀ᵐ x ∂μ, x ∈ E → ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Matrix.diagonal a * B x = B x * C := by
  classical
  have hchanges : ∀ᵐ x ∂μ, ∃ R : Matrix (Fin k) (Fin k) ℝ,
      R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R := by
    filter_upwards [hE, hzero, hT.quasiMeasurePreserving.ae hzero,
      hT.quasiMeasurePreserving.ae hfull, htransport] with x hEx hz hzT hfT ht
    by_cases hx : x ∈ E
    · exact exists_invertible_frame_change (Matrix.diagonal a * B x)
        (B (T x)) (hfT (hEx.mpr hx)) (ht hx).le
    · refine ⟨1, by simp, ?_⟩
      rw [hz hx, hzT (fun h => hx (hEx.mp h))]
      simp
  let R : Y → Matrix (Fin k) (Fin k) ℝ := fun x =>
    if h : ∃ R : Matrix (Fin k) (Fin k) ℝ,
        R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R then
      Classical.choose h else 1
  have hR : ∀ᵐ x ∂μ, (R x).det ≠ 0 := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).1
  have hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).2
  filter_upwards [hfull,
    ae_frame_minors_have_one_diagonal_weight μ T hT B hB a ha R hR hcov]
    with x hx hweights hxE
  obtain ⟨p, hp⟩ := exists_nonzero_frameMinor_of_linearIndependent (B x) (hx hxE)
  refine ⟨((B x).submatrix p id)⁻¹ * Matrix.diagonal (fun u => a (p u)) *
    (B x).submatrix p id, ?_⟩
  apply diagonal_mul_frame_of_minor_weights (B x) p hp a (fun i => ne_of_gt (ha i))
  intro q hq
  exact (hweights q p hq).resolve_right hp

end DukePrimeDegree

end

end OAI
