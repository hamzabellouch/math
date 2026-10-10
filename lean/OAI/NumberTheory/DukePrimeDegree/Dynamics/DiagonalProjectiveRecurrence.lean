import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalRecurrence

namespace OAI

/-!
# Finite invariant projective laws of a positive diagonal map

This is a coordinate form of diagonal recurrence. A measurable nonzero
representative may change by an arbitrary nonzero scalar under the
dynamics. Ratios cancel that scalar. Unequal positive diagonal weights
cannot both occur in the support of a representative almost everywhere.
The conclusion is an actual eigenline statement, not an orbit hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree

lemma ratio_of_common_nonzero_scalar
    (r a b u v : ℝ) (hr : r ≠ 0) (hb : b ≠ 0) :
    (r * a * u) / (r * b * v) = (a / b) * (u / v) := by
  by_cases hv : v = 0
  · simp only [hv, mul_zero, div_zero]
  · field_simp [hr, hb, hv]

theorem ae_coordinate_zero_or_zero_of_diagonal_weights
    {Y I : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (w : Y → I → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (r : Y → ℝ) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hcov : ∀ i, (fun x => w (T x) i) =ᵐ[μ] fun x => r x * a i * w x i)
    (i j : I) (hij : a j < a i) :
    ∀ᵐ x ∂μ, w x i = 0 ∨ w x j = 0 := by
  have he : (fun x => w (T x) i / w (T x) j) =ᵐ[μ]
      fun x => (a i / a j) * (w x i / w x j) := by
    filter_upwards [hr, hcov i, hcov j] with x hx hi hj
    rw [hi, hj]
    exact ratio_of_common_nonzero_scalar (r x) (a i) (a j)
      (w x i) (w x j) hx (ne_of_gt (ha j))
  have hz := ae_eq_zero_of_expanding_covariance μ T hT
    (fun x => w x i / w x j) ((hw i).div (hw j)) (a i / a j)
    ((one_lt_div (ha j)).mpr hij) he
  filter_upwards [hz] with x hx
  exact div_eq_zero_iff.mp hx

/-- Unequal weights do not coexist in a nonzero projective coordinate
representative. Only countably many coordinates are needed. -/
theorem ae_diagonal_projective_single_weight
    {Y I : Type*} [MeasurableSpace Y] [Countable I]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (w : Y → I → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (r : Y → ℝ) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hcov : ∀ i, (fun x => w (T x) i) =ᵐ[μ] fun x => r x * a i * w x i) :
    ∀ᵐ x ∂μ, ∀ i j, a i ≠ a j → w x i = 0 ∨ w x j = 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : a i = a j
  · exact Eventually.of_forall (fun _ h => (h hij).elim)
  · rcases lt_or_gt_of_ne hij with h | h
    · exact (ae_coordinate_zero_or_zero_of_diagonal_weights μ T hT w hw a ha r hr
        hcov j i h).mono fun x hx _ => hx.symm
    · exact (ae_coordinate_zero_or_zero_of_diagonal_weights μ T hT w hw a ha r hr
        hcov i j h).mono fun _ hx _ => hx

/-- The projective representative lies in one genuine eigenspace of
the positive diagonal operator almost everywhere. -/
theorem ae_diagonal_projective_eigenline
    {Y I : Type*} [MeasurableSpace Y] [Countable I]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (w : Y → I → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (hne : ∀ᵐ x ∂μ, ∃ i, w x i ≠ 0)
    (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (r : Y → ℝ) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hcov : ∀ i, (fun x => w (T x) i) =ᵐ[μ] fun x => r x * a i * w x i) :
    ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ i, a i * w x i = c * w x i := by
  filter_upwards [hne, ae_diagonal_projective_single_weight μ T hT w hw a ha r hr hcov]
    with x hx hsingle
  obtain ⟨i, hi⟩ := hx
  refine ⟨a i, ha i, ?_⟩
  intro j
  by_cases hji : a j = a i
  · rw [hji]
  · have hj : w x j = 0 := (hsingle j i hji).resolve_right hi
    rw [hj, mul_zero, mul_zero]

end DukePrimeDegree

end

end OAI
