import OAI.NumberTheory.DukePrimeDegree.Geometry.RowLongBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.RowTimeSplit

namespace OAI

/-!
# Rectangular row boxes

Sup-norm row cubes split into a remaining-coordinate cube and a real
interval. Free row orbits admit boxes with exactly these time domains,
so the row-to-single-root coordinate change preserves product boxes.
-/

noncomputable section
open Matrix Set Metric
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowCube {n : ℕ} (i : Fin n) (R : ℝ) : Set (RowTime i) :=
  {a | ∀ j, |a.val j| < R}

def rowRemainingCube {n : ℕ} (i j : Fin n) (R : ℝ) : Set (RowRemainingTime i j) :=
  {a | ∀ l, |a.val.val l| < R}

lemma rowCube_eq_ball {n : ℕ} (i : Fin n) {R : ℝ} (hR : 0 < R) :
    rowCube i R = ball 0 R := by
  ext a
  change (∀ j, |a.val j| < R) ↔ dist a 0 < R
  rw [dist_zero_right]
  change (∀ j, |a.val j| < R) ↔ ‖a.val‖ < R
  have h : ‖a.val‖ < R ↔ ∀ j, ‖a.val j‖ < R := pi_norm_lt_iff hR
  simpa only [Real.norm_eq_abs] using h.symm

lemma isOpen_rowCube {n : ℕ} (i : Fin n) {R : ℝ} (hR : 0 < R) :
    IsOpen (rowCube i R) := by rw [rowCube_eq_ball i hR]; exact isOpen_ball

lemma isOpen_rowRemainingCube {n : ℕ} (i j : Fin n) (R : ℝ) :
    IsOpen (rowRemainingCube i j R) := by
  change IsOpen {a : RowRemainingTime i j | ∀ l, |a.val.val l| < R}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro l
  exact isOpen_lt (((continuous_apply l).comp
    (continuous_subtype_val.comp continuous_subtype_val)).abs) continuous_const

theorem rowTimeSplit_cube {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {R : ℝ} (hR : 0 < R) :
    (rowTimeSplit hij).symm ⁻¹' rowCube i R = rowRemainingCube i j R ×ˢ Ioo (-R) R := by
  ext z
  obtain ⟨w, t⟩ := z
  have hj : ((rowTimeSplit hij).symm (w, t)).val j = t := by
    simp [rowTimeSplit, rowRemainingTime_self, rowUnit_apply_self]
  have hl (l : Fin n) (hlj : l ≠ j) :
      ((rowTimeSplit hij).symm (w, t)).val l = w.val.val l := by
    simp [rowTimeSplit, rowUnit, hlj]
  change (∀ l, |((rowTimeSplit hij).symm (w, t)).val l| < R) ↔
    (∀ l, |w.val.val l| < R) ∧ -R < t ∧ t < R
  constructor
  · intro h
    refine ⟨?_, abs_lt.mp (by simpa only [hj] using h j)⟩
    intro l
    by_cases hlj : l = j
    · subst l
      simpa only [rowRemainingTime_self, abs_zero] using hR
    · simpa only [hl l hlj] using h l
  · rintro ⟨hw, ht⟩ l
    by_cases hlj : l = j
    · subst l
      rw [hj]
      exact abs_lt.mpr ht
    · rw [hl l hlj]
      exact hw l

theorem rowRootBox_with_cube_time {n : ℕ} (i k : Fin n)
    (s : RowRootSlice i k)
    (hinj : Function.Injective (fun a : RowTime i => rowQuotientParametrization i k (s, a)))
    {R : ℝ} (hR : 0 < R) :
    ∃ B : RowRootBox i k, s ∈ B.transverse ∧ B.time = rowCube i R := by
  obtain ⟨B, hs, hK⟩ := rowRootBox_contains_compact_time i k s hinj
    (closedBall 0 R) (isCompact_closedBall 0 R)
  have hsub : B.transverse ×ˢ rowCube i R ⊆ B.domain := by
    rintro ⟨y, a⟩ ⟨hy, ha⟩
    refine ⟨hy, hK ?_⟩
    apply ball_subset_closedBall
    rwa [← rowCube_eq_ball i hR]
  have he := B.embedding.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((B.transverse_open.prod (isOpen_rowCube i hR)).preimage continuous_subtype_val))
  exact ⟨⟨B.transverse, rowCube i R, B.transverse_open, isOpen_rowCube i hR, he⟩, hs, rfl⟩

end DukePrimeDegree

end

end OAI
