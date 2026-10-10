import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Basic
import OAI.Combinatorics.IndependentSets.Repetition.TraceLaw

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

section

variable {α : Type*} [Fintype α]

private theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

theorem rectangle_row_mass (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : density a ∈ thresholds) (h0 : 0 ≤ density a) (h1 : density a ≤ 1) :
    (∑ i, if rectangleAccept thresholds density (a, i) then
      rectangleWeight thresholds (a, i) else 0) = density a / (Fintype.card α : ℝ) := by
  calc
    _ = (∑ i : Fin (thresholdPartition thresholds).length,
        if (thresholdPartition thresholds)[i].lo < density a then
          (thresholdPartition thresholds)[i].hi - (thresholdPartition thresholds)[i].lo else 0) /
        (Fintype.card α : ℝ) := by
      rw [sum_div_const]
      apply Finset.sum_congr rfl
      intro i _
      simp [rectangleAccept, rectangleWeight, ite_div]
    _ = density a / (Fintype.card α : ℝ) := by
      rw [sum_interval_get (fun I => if I.lo < density a then I.hi - I.lo else 0),
        partition_acceptance_mass thresholds (density a) hm h0 h1]

theorem rectangle_acceptance_mass (thresholds : List ℝ) (density : α → ℝ)
    (hm : ∀ a, density a ∈ thresholds) (h0 : ∀ a, 0 ≤ density a)
    (h1 : ∀ a, density a ≤ 1) :
    eventMass (rectangleWeight thresholds) (rectangleAccept thresholds density) =
      (∑ a, density a) / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [rectangle_row_mass thresholds density _ (hm _) (h0 _) (h1 _)]
  rw [sum_div_const]

theorem rectangle_label_mass [DecidableEq α] (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : ∀ x, density x ∈ thresholds) (h0 : ∀ x, 0 ≤ density x)
    (h1 : ∀ x, density x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds density seed && decide (seed.1 = a)) =
      density a / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : α, if x = a then density x / (Fintype.card α : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · simpa [hx] using rectangle_row_mass thresholds density x (hm x) (h0 x) (h1 x)
      · simp [hx]
    _ = density a / (Fintype.card α : ℝ) := by simp

omit [Fintype α] in theorem rectangle_and (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => min (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

omit [Fintype α] in theorem rectangle_or (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => max (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

theorem max_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : max x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [max_def, h, hx, hy]

theorem rectangle_union_mass (thresholds : List ℝ) (p q : α → ℝ)
    (hpm : ∀ a, p a ∈ thresholds) (hqm : ∀ a, q a ∈ thresholds)
    (hp0 : ∀ a, 0 ≤ p a) (_hq0 : ∀ a, 0 ≤ q a)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ a, q a ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      unionMass p q / (Fintype.card α : ℝ) := by
  rw [rectangle_or]
  exact rectangle_acceptance_mass thresholds _
    (fun a => max_mem_thresholds thresholds (hpm a) (hqm a))
    (fun a => (hp0 a).trans (le_max_left _ _)) (fun a => max_le (hp1 a) (hq1 a))

theorem rectangle_common_label_mass [DecidableEq α] (thresholds : List ℝ)
    (p q : α → ℝ) (a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (_hq1 : ∀ x, q x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => (rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) &&
        decide (seed.1 = a)) = min (p a) (q a) / (Fintype.card α : ℝ) := by
  have hand := congrFun (rectangle_and thresholds p q)
  simp_rw [hand]
  exact rectangle_label_mass thresholds _ a
    (fun x => min_mem_thresholds thresholds (hpm x) (hqm x))
    (fun x => le_min (hp0 x) (hq0 x)) (fun x => (min_le_left _ _).trans (hp1 x))

end

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
