import OAI.MeasureTheory.Falconer.Angular.AngularGainFinite
import Mathlib.Data.Int.Interval

namespace OAI

/-!
# A common line grid for the planar incidence obstruction

Each original strip gives a bounded list of common-grid line parameters.
The list is attached to its original direction label. Rounding therefore
turns the manuscript's covering-number upper bound into the cardinality
upper bound needed by `published_furstenberg_labelled_obstruction`.
-/

namespace Falconer
open Set

noncomputable def gridLine (δ : ℝ) (p : ℤ × ℤ) : Space 2 :=
  WithLp.toLp 2 ![δ * (p.1 : ℝ), δ * (p.2 : ℝ)]

@[simp] theorem gridLine_fst (δ : ℝ) (p : ℤ × ℤ) :
    gridLine δ p 0 = δ * (p.1 : ℝ) := rfl

@[simp] theorem gridLine_snd (δ : ℝ) (p : ℤ × ℤ) :
    gridLine δ p 1 = δ * (p.2 : ℝ) := rfl

private theorem integer_grid_separation {δ : ℝ} (hδ : 0 < δ) {i j : ℤ}
    (hij : i ≠ j) : δ ≤ |δ * (i : ℝ) - δ * (j : ℝ)| := by
  have hzpos : (0 : ℤ) < |i - j| := abs_pos.mpr (sub_ne_zero.mpr hij)
  have hz : (1 : ℤ) ≤ |i - j| := by omega
  have hr : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by exact_mod_cast hz
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * |(i : ℝ) - (j : ℝ)| := mul_le_mul_of_nonneg_left hr hδ.le
    _ = |δ * (i : ℝ) - δ * (j : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hδ]

theorem gridLine_dist_ge {δ : ℝ} (hδ : 0 < δ) {p q : ℤ × ℤ} (hpq : p ≠ q) :
    δ ≤ dist (gridLine δ p) (gridLine δ q) := by
  by_cases hfst : p.1 = q.1
  · have hsnd : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfst h)
    calc
      δ ≤ |δ * (p.2 : ℝ) - δ * (q.2 : ℝ)| := integer_grid_separation hδ hsnd
      _ = dist (gridLine δ p 1) (gridLine δ q 1) := by
        rw [gridLine_snd, gridLine_snd, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 1
  · calc
      δ ≤ |δ * (p.1 : ℝ) - δ * (q.1 : ℝ)| := integer_grid_separation hδ hfst
      _ = dist (gridLine δ p 0) (gridLine δ q 0) := by
        rw [gridLine_fst, gridLine_fst, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 0

theorem gridLine_injective {δ : ℝ} (hδ : 0 < δ) : Function.Injective (gridLine δ) := by
  intro p q h
  by_contra hpq
  have hsep := gridLine_dist_ge hδ hpq
  rw [h, dist_self] at hsep
  exact hδ.not_ge hsep

/-- Every finite subfamily of the common line grid is δ-separated. -/
theorem gridLine_image_separated {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ)) :
    FiniteSeparatedAt δ (S.image (gridLine δ)) := by
  classical
  intro x hx y hy hxy
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
  apply gridLine_dist_ge hδ
  intro hpq
  exact hxy (congrArg (gridLine δ) hpq)

theorem roundedIncidentLine_family_separated {ι : Type*} [DecidableEq ι]
    {δ : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ) (D : Finset ι) :
    FiniteSeparatedAt δ (D.image (fun i => roundedIncidentLine δ x (m i))) := by
  intro l hl l' hl' hll'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl'
  apply gridLine_dist_ge hδ
    (p := (round (m i / δ), round ((x 1 - lineGridRound δ (m i) * x 0) / δ)))
    (q := (round (m j / δ), round ((x 1 - lineGridRound δ (m j) * x 0) / δ)))
  intro heq
  exact hll' (congrArg (gridLine δ) heq)

/-- A fixed smaller chart leaves room for rounding while staying inside
the unit chart used by the published finite theorem. -/
theorem roundedIncidentLine_in_chart {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (x : Space 2) (hx0 : |x 0| ≤ 1 / 4) (hx1 : |x 1| ≤ 1 / 4)
    (m : ℝ) (hm : |m| ≤ 1 / 2) :
    |roundedIncidentLine δ x m 0| ≤ 1 ∧ |roundedIncidentLine δ x m 1| ≤ 1 := by
  have hM : |lineGridRound δ m| ≤ 1 := by
    have hsum := abs_sub_le (lineGridRound δ m) m 0
    have herr := lineGridRound_error hδ m
    rw [sub_zero, sub_zero, abs_sub_comm (lineGridRound δ m)] at hsum
    linarith
  constructor
  · exact hM
  · have ht : |x 1 - lineGridRound δ m * x 0| ≤ 1 / 2 := by
      have hprod : |lineGridRound δ m * x 0| ≤ 1 / 4 := by
        rw [abs_mul]
        exact (mul_le_mul hM hx0 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      have htri : |x 1 - lineGridRound δ m * x 0| ≤
          |x 1| + |lineGridRound δ m * x 0| := by
        simpa using abs_sub_le (x 1) 0 (lineGridRound δ m * x 0)
      exact htri.trans (by linarith)
    have hsum := abs_sub_le
      (lineGridRound δ (x 1 - lineGridRound δ m * x 0))
      (x 1 - lineGridRound δ m * x 0) 0
    have herr := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
    rw [sub_zero, sub_zero, abs_sub_comm (lineGridRound δ (x 1 - lineGridRound δ m * x 0))]
      at hsum
    change |lineGridRound δ (x 1 - lineGridRound δ m * x 0)| ≤ 1
    linarith

/-- The bounded candidate intercept list for one strip, retaining its
original slope label even if other labels have the same rounded slope. -/
noncomputable def roundedStripCandidates (δ m a : ℝ) (L : ℕ) : Finset (Space 2) :=
  (Finset.Icc (round (a / δ) - (L : ℤ)) (round (a / δ) + (L : ℤ))).image
    (fun j => gridLine δ (round (m / δ), j))

theorem roundedStripCandidates_card_le (δ m a : ℝ) (L : ℕ) :
    (roundedStripCandidates δ m a L).card ≤ 2 * L + 1 := by
  classical
  calc
    (roundedStripCandidates δ m a L).card ≤
        (Finset.Icc (round (a / δ) - (L : ℤ)) (round (a / δ) + (L : ℤ))).card :=
      Finset.card_image_le
    _ = 2 * L + 1 := by
      rw [Int.card_Icc]
      omega

/-- A rounded line through any point of a strip belongs to that strip's
bounded candidate list. This is the fixed-width loss in `ang:planar-measures`. -/
theorem roundedIncidentLine_mem_candidates {δ C a m : ℝ} (hδ : 0 < δ)
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hstrip : |x 1 - m * x 0 - a| ≤ C * δ)
    (L : ℕ) (hL : C + 2 ≤ (L : ℝ)) :
    roundedIncidentLine δ x m ∈ roundedStripCandidates δ m a L := by
  classical
  let j : ℤ := round ((x 1 - lineGridRound δ m * x 0) / δ)
  let j₀ : ℤ := round (a / δ)
  have hnear : |δ * (j : ℝ) - a| ≤ (C + 1) * δ :=
    roundedIncidentLine_near_strip hδ x hx hstrip
  have hcenter : |a - δ * (j₀ : ℝ)| ≤ δ / 2 := lineGridRound_error hδ a
  have hsum : |δ * (j : ℝ) - δ * (j₀ : ℝ)| ≤ δ * (L : ℝ) := by
    have htri := (abs_sub_le (δ * (j : ℝ)) a (δ * (j₀ : ℝ))).trans
      (add_le_add hnear hcenter)
    exact htri.trans (by nlinarith)
  have habs : |(j : ℝ) - (j₀ : ℝ)| ≤ (L : ℝ) := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    calc
      δ * |(j : ℝ) - (j₀ : ℝ)| = |δ * (j : ℝ) - δ * (j₀ : ℝ)| := by
        rw [← mul_sub, abs_mul, abs_of_pos hδ]
      _ ≤ δ * (L : ℝ) := hsum
  have hint : |j - j₀| ≤ (L : ℤ) := by exact_mod_cast habs
  have hbounds := abs_le.mp hint
  have hmem : round (a / δ) - (L : ℤ) ≤ j ∧ j ≤ round (a / δ) + (L : ℤ) := by
    change j₀ - (L : ℤ) ≤ j ∧ j ≤ j₀ + (L : ℤ)
    omega
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_Icc.mpr hmem, rfl⟩

end Falconer

end OAI
