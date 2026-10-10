import OAI.MeasureTheory.Falconer.Incidence.PublishedFurstenberg
import Mathlib.Algebra.Order.Round

namespace OAI

/-!
# Finite labelled incidence obstruction

The sampling argument in `ang:planar-measures` ends with finite point
and line families. Their counting contradiction follows
from the precise published Furstenberg input. All line families must use
a common separated grid before cardinalities replace covering numbers.
Direction labels remain distinct throughout the upper counting estimate.
-/

namespace Falconer
open Set
open scoped BigOperators

/-- A labelled family bounds a union even when two labels have the same
geometric coordinate. No identification of their fibers is required. -/
theorem labelled_line_union_card_le {ι : Type*} [DecidableEq ι]
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (D : Finset ι) (U : ι → Finset (Space 2)) {L : ℝ}
    (hcover : ∀ x ∈ P, ∀ l ∈ T x, ∃ i ∈ D, l ∈ U i)
    (hU : ∀ i ∈ D, ((U i).card : ℝ) ≤ L) :
    ((P.biUnion T).card : ℝ) ≤ (D.card : ℝ) * L := by
  classical
  have hsub : P.biUnion T ⊆ D.biUnion U := by
    intro l hl
    obtain ⟨x, hx, hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨i, hi, hli⟩ := hcover x hx l hl
    exact Finset.mem_biUnion.mpr ⟨i, hi, hli⟩
  calc
    ((P.biUnion T).card : ℝ) ≤ ((D.biUnion U).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ D, ((U i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D) (t := U))
    _ ≤ ∑ _i ∈ D, L := Finset.sum_le_sum hU
    _ = (D.card : ℝ) * L := by simp

/-- After the two sampling steps, fewer than `δ^(-b-ε/4)` labels with
fewer than that many line cells per label contradict the published
Furstenberg estimate. This is the final quantitative contradiction in
the planar measure-incidence argument. -/
theorem published_furstenberg_labelled_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1 / 2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ ^ (-ε)) P →
    ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
        FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b (δ ^ (-ε)) (T x) ∧
        ∀ l ∈ T x, TubeIncident δ x l) →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (U : ι → Finset (Space 2)),
      (D.card : ℝ) ≤ δ ^ (-b - ε / 4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ ^ (-b - ε / 4)) →
      (∀ x ∈ P, ∀ l ∈ T x, ∃ i ∈ D, l ∈ U i) → False := by
  obtain ⟨ε, δ₀, hε, hδ₀, hδ₀1, hF⟩ := hpublished b f hb hb' hbf hf
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hball T hT ι _ D U hD hU hcover
  have hδ1 : δ < 1 := hδsmall.trans_le hδ₀1
  have hlower := hF δ hδ hδsmall P hP hchart hsep hball T hT
  have hupper := labelled_line_union_card_le P T D U hcover hU
  have hcard : ((P.biUnion T).card : ℝ) ≤ δ ^ (-2 * b - ε / 2) := by
    calc
      ((P.biUnion T).card : ℝ) ≤ (D.card : ℝ) * δ ^ (-b - ε / 4) := hupper
      _ ≤ δ ^ (-b - ε / 4) * δ ^ (-b - ε / 4) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-2 * b - ε / 2) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
  have hstrict : δ ^ (-2 * b - ε / 2) < δ ^ (-2 * b - ε) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  exact (not_lt_of_ge (hlower.trans hcard)) hstrict

/-- Rounding a line coordinate to a grid of mesh `δ`. -/
noncomputable def lineGridRound (δ a : ℝ) : ℝ := δ * (round (a / δ) : ℝ)

theorem lineGridRound_error {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    |a - lineGridRound δ a| ≤ δ / 2 := by
  have h := abs_sub_round (a / δ)
  calc
    |a - lineGridRound δ a| = |δ * (a / δ - (round (a / δ) : ℝ))| := by
      congr 1
      simp only [lineGridRound]
      field_simp
    _ = δ * |a / δ - (round (a / δ) : ℝ)| := by rw [abs_mul, abs_of_pos hδ]
    _ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left h hδ.le
    _ = δ / 2 := by ring

/-- Choose the grid slope first, then the grid intercept nearest the exact
line through the point. Every constructed line remains incident. -/
noncomputable def roundedIncidentLine (δ : ℝ) (x : Space 2) (m : ℝ) : Space 2 :=
  WithLp.toLp 2 ![lineGridRound δ m,
    lineGridRound δ (x 1 - lineGridRound δ m * x 0)]

@[simp] theorem roundedIncidentLine_fst (δ : ℝ) (x : Space 2) (m : ℝ) :
    roundedIncidentLine δ x m 0 = lineGridRound δ m := rfl

@[simp] theorem roundedIncidentLine_snd (δ : ℝ) (x : Space 2) (m : ℝ) :
    roundedIncidentLine δ x m 1 =
      lineGridRound δ (x 1 - lineGridRound δ m * x 0) := rfl

theorem roundedIncidentLine_incident {δ : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ℝ) :
    TubeIncident δ x (roundedIncidentLine δ x m) := by
  have herr := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
  have hsqrt : 1 ≤ Real.sqrt (1 + (lineGridRound δ m) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (lineGridRound δ m)]
  change |x 1 - lineGridRound δ m * x 0 -
      lineGridRound δ (x 1 - lineGridRound δ m * x 0)| /
      Real.sqrt (1 + (lineGridRound δ m) ^ 2) ≤ δ
  exact (div_le_self (abs_nonneg _) hsqrt).trans (herr.trans (by linarith))

/-- A strip in one original direction contains only a bounded interval of
grid intercepts after rounding that direction. The interval is uniform
in its original label, so coincident directions need not share covers. -/
theorem roundedIncidentLine_near_strip {δ C a m : ℝ} (hδ : 0 < δ)
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hstrip : |x 1 - m * x 0 - a| ≤ C * δ) :
    |roundedIncidentLine δ x m 1 - a| ≤ (C + 1) * δ := by
  have hms := lineGridRound_error hδ m
  have hi := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
  have htilt : |(m - lineGridRound δ m) * x 0| ≤ δ / 2 := by
    rw [abs_mul]
    exact (mul_le_mul hms hx (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  calc
    |roundedIncidentLine δ x m 1 - a| ≤
        |roundedIncidentLine δ x m 1 - (x 1 - lineGridRound δ m * x 0)| +
        |(x 1 - lineGridRound δ m * x 0) - a| := abs_sub_le _ _ _
    _ = |(x 1 - lineGridRound δ m * x 0) - roundedIncidentLine δ x m 1| +
        |(x 1 - m * x 0 - a) + (m - lineGridRound δ m) * x 0| := by
      rw [abs_sub_comm (roundedIncidentLine δ x m 1)]
      congr 2
      ring
    _ ≤ δ / 2 + (C * δ + δ / 2) := by
      apply add_le_add hi
      exact (abs_add_le _ _).trans (add_le_add hstrip htilt)
    _ = (C + 1) * δ := by ring

end Falconer

end OAI
