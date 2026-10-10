import Mathlib

namespace OAI

universe uAlpha

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326

-- The existence form avoids imposing any continuity on the chosen tolerance.
theorem exists_sign_tolerance {d : ℕ} (D : Finset (Fin d → ℝ))
    (r : Fin d → ℝ) :
    ∃ E : ℝ, 0 < E ∧ E ≤ 1 / 2 ∧
      ∀ p : Fin d → ℝ, (∀ i, |p i - r i| < E) →
        ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
          |(∑ i, p i * v i) - (∑ i, r i * v i)| <
            |∑ i, r i * v i| / 2 := by
  classical
  have hnear : ∀ᶠ p : Fin d → ℝ in 𝓝 r,
      ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
        |(∑ i, p i * v i) - (∑ i, r i * v i)| <
          |∑ i, r i * v i| / 2 := by
    apply (Filter.eventually_all_finset D).2
    intro v hv
    by_cases hz : (∑ i, r i * v i) = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hz).elim)
    · have hc : Continuous (fun p : Fin d → ℝ =>
          |(∑ i, p i * v i) - (∑ i, r i * v i)|) := by
        fun_prop
      have hp : (0 : ℝ) < |∑ i, r i * v i| / 2 :=
        div_pos (abs_pos.mpr hz) (by norm_num)
      have he := (hc.continuousAt (x := r)).eventually_lt_const
        (show |(∑ i, r i * v i) - (∑ i, r i * v i)| <
          |∑ i, r i * v i| / 2 by simpa using hp)
      exact he.mono (fun p h _ => h)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro p hp
  apply hball
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  rw [Real.dist_eq]
  exact (hp i).trans_le (min_le_left _ _)

/-- A perturbation smaller than half a nonzero value preserves its sign and half-gap. -/
theorem sign_and_half_gap_of_abs_sub_lt {p r : ℝ} (hr : r ≠ 0)
    (hclose : |p - r| < |r| / 2) :
    (0 < p ↔ 0 < r) ∧ (p < 0 ↔ r < 0) ∧ |r| / 2 < |p| := by
  rcases lt_or_gt_of_ne hr with hr | hr
  · rw [abs_of_neg hr] at hclose
    have hb := abs_lt.mp hclose
    have hp : p < 0 := by linarith [hb.2]
    refine ⟨iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hr.le),
      iff_of_true hp hr, ?_⟩
    rw [abs_of_neg hp, abs_of_neg hr]
    linarith [hb.2]
  · rw [abs_of_pos hr] at hclose
    have hb := abs_lt.mp hclose
    have hp : 0 < p := by linarith [hb.1]
    refine ⟨iff_of_true hp hr,
      iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hr.le), ?_⟩
    rw [abs_of_pos hp, abs_of_pos hr]
    linarith [hb.1]

/-- Any finite family of positive real numbers has a common positive lower bound. -/
theorem finite_positive_lower_bound {α : Type uAlpha} (S : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ a ∈ S, H ≤ f a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨H, hH, hHone, hHf⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
      refine ⟨min H (f a), lt_min hH (hf a (Finset.mem_insert_self _ _)),
        (min_le_left _ _).trans hHone, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hHf b hb)

/-- In a fixed finite slope family, all nonzero comparisons have a uniform half-gap. -/
theorem exists_uniform_dot_gap {d : ℕ} (R D : Finset (Fin d → ℝ)) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧
      ∀ r ∈ R, ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
        H ≤ |∑ i, r i * v i| / 2 := by
  classical
  let S := (R.product D).filter (fun rv => (∑ i, rv.1 i * rv.2 i) ≠ 0)
  obtain ⟨H, hH, hHone, hHgap⟩ := finite_positive_lower_bound S
    (fun rv => |∑ i, rv.1 i * rv.2 i| / 2) (by
      intro rv hrv
      exact div_pos (abs_pos.mpr (Finset.mem_filter.mp hrv).2) (by norm_num))
  refine ⟨H, hH, hHone, ?_⟩
  intro r hr v hv hne
  exact hHgap (r, v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, hv⟩, hne⟩)

/-- The tolerance can be selected pointwise; no regularity of it is required. -/
theorem exists_sign_tolerance_function {d : ℕ} (D : Finset (Fin d → ℝ)) :
    ∃ E : (Fin d → ℝ) → ℝ,
      (∀ r, 0 < E r ∧ E r ≤ 1 / 2) ∧
      ∀ r p : Fin d → ℝ, (∀ i, |p i - r i| < E r) →
        ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
          (0 < (∑ i, p i * v i) ↔ 0 < (∑ i, r i * v i)) ∧
          ((∑ i, p i * v i) < 0 ↔ (∑ i, r i * v i) < 0) ∧
          |∑ i, r i * v i| / 2 < |∑ i, p i * v i| := by
  choose E hEpos hEbound hEclose using exists_sign_tolerance D
  refine ⟨E, fun r => ⟨hEpos r, hEbound r⟩, ?_⟩
  intro r p hp v hv hne
  exact sign_and_half_gap_of_abs_sub_lt hne (hEclose r p hp v hv hne)

end Problem326

end

end OAI
