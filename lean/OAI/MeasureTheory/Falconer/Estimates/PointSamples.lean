import OAI.MeasureTheory.Falconer.Angular.AngularSamples

namespace OAI

/-!
# Separated point sets from samples with repeated coordinates

A maximal separated subfamily covers the sampled coordinates. The bound
on the multiplicity in a small ball then controls the loss in cardinality.
This is the point-selection step of `ang:planar-measures`.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem exists_separated_cover (S : Finset (Space 2)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ P : Finset (Space 2), P ⊆ S ∧ FiniteSeparatedAt δ P ∧
      ∀ x ∈ S, ∃ y ∈ P, dist x y ≤ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp [FiniteSeparatedAt], by simp⟩
  | @insert x S _ ih =>
    obtain ⟨P, hPS, hsep, hcover⟩ := ih
    by_cases hx : ∃ y ∈ P, dist x y ≤ δ
    · refine ⟨P, hPS.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact hcover z hz
    · refine ⟨insert x P, Finset.insert_subset_insert x hPS, ?_, ?_⟩
      · intro u hu v hv hne
        rcases Finset.mem_insert.mp hu with hue | huP
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · exact (hne (hue.trans hve.symm)).elim
          · rw [hue]
            exact (lt_of_not_ge (fun h => hx ⟨v, hvP, h⟩)).le
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · rw [hve, dist_comm]
            exact (lt_of_not_ge (fun h => hx ⟨u, huP, h⟩)).le
          · exact hsep u huP v hvP hne
      · intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · exact ⟨x, Finset.mem_insert_self _ _, by simpa only [hzx, dist_self] using hδ⟩
        · obtain ⟨y, hy, hdist⟩ := hcover z hz
          exact ⟨y, Finset.mem_insert_of_mem hy, hdist⟩

/-- Distinct selected coordinates in a ball cannot outnumber the original
sample labels in that ball. -/
theorem selected_points_ball_count {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    (hP : P ⊆ D.image p) (z : Space 2) (r : ℝ) :
    (P.filter (fun x => dist x z ≤ r)).card ≤
      (D.filter (fun i => dist (p i) z ≤ r)).card := by
  classical
  have hsub : P.filter (fun x => dist x z ≤ r) ⊆
      (D.filter (fun i => dist (p i) z ≤ r)).image p := by
    intro x hx
    obtain ⟨hxP, hdist⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hP hxP)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hdist⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Covering the original labels by the selected point balls gives the
lower cardinality bound, with all repeated labels counted. -/
theorem selected_points_card_lower {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ L : ℝ} (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hcount : ∀ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) ≤ L) :
    (D.card : ℝ) ≤ (P.card : ℝ) * L := by
  classical
  have hsub : D ⊆ P.biUnion (fun x => D.filter (fun i => dist (p i) x ≤ δ)) := by
    intro i hi
    obtain ⟨x, hx, hdist⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hi, hdist⟩⟩
  calc
    (D.card : ℝ) ≤ ((P.biUnion (fun x => D.filter
        (fun i => dist (p i) x ≤ δ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P, L := Finset.sum_le_sum hcount
    _ = (P.card : ℝ) * L := by simp

/-- The selected separated point set has the normalized finite ball
bound required by the published Furstenberg theorem. -/
theorem selected_points_normalized_ball_bound {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ K f : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hP : P ⊆ D.image p)
    (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    NormalizedFiniteBallBound δ f (2 * K^2) P := by
  have hn : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have hlow := selected_points_card_lower D p P hcover (fun x _ => hcount x δ le_rfl)
  have hbase : 1 ≤ (P.card : ℝ) * K * δ ^ f := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hlow]
  have hcoef : K * (D.card : ℝ) ≤ (2 * K^2) * (P.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hbase (show 0 ≤ K * (D.card : ℝ) by positivity)
    have hupper := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ (P.card : ℝ) * K^2 by positivity)
    nlinarith
  intro z r hδr _
  calc
    ((P.filter (fun x => dist x z ≤ r)).card : ℝ) ≤
        ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) := by
      exact_mod_cast selected_points_ball_count D p P hP z r
    _ ≤ K * (D.card : ℝ) * r ^ f := hcount z r hδr
    _ ≤ ((2 * K^2) * (P.card : ℝ)) * r ^ f :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    _ = _ := by ring

theorem exists_separated_point_sample {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) {δ K f : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    ∃ P : Finset (Space 2), P.Nonempty ∧ P ⊆ D.image p ∧
      FiniteSeparatedAt δ P ∧ NormalizedFiniteBallBound δ f (2 * K^2) P := by
  obtain ⟨P, hP, hsep, hcover⟩ := exists_separated_cover (D.image p) hδ.le
  have hcover' : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ :=
    fun i hi => hcover (p i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨i, hi⟩ := hD
  obtain ⟨x, hx, _⟩ := hcover' i hi
  exact ⟨P, ⟨x, hx⟩, hP, hsep,
    selected_points_normalized_ball_bound D p P hδ hK ⟨i, hi⟩ hP hcover' hsize hcount⟩

end Falconer

end OAI
