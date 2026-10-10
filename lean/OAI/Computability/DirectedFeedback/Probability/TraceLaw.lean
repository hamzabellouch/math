import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineProductFinish

namespace OAI


namespace DFVSGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) (c : ℝ) :
    traceAverage w n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

end


noncomputable section

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def splitPoint (I : ThresholdInterval) (t : ℝ) : ℝ := max I.lo (min t I.hi)

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih


variable {α : Type*} [Fintype α]

private theorem sum_div_const_inline_Rectangle {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
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
    rw [← sum_div_const_inline_Rectangle, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
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
      rw [sum_div_const_inline_Rectangle]
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
  rw [sum_div_const_inline_Rectangle]

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


noncomputable section

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


variable [Fintype α] [Nonempty α]

theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h


end


open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

private theorem nonnegative_powers_mono_inline_SharedProfiles (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ) : a ^ n ≤ b ^ n := by
  have hb : 0 ≤ b := le_trans ha hab
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg hb n)

theorem sharedProfile_label_diagonal_bound [Nonempty S] [DecidableEq S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) (fallback a : S) (n : ℕ) :
    min ((L x).weight a) ((R y).weight a) /
        (1 + totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      traceAverage (rectangleWeight (sharedProfileThresholds L R)) n
        (localDiagonal (sharedProfileLeft L R x) (sharedProfileRight L R y)
          Prod.fst fallback a) := by
  have hp := nonnegative_powers_mono_inline_SharedProfiles (sharedProfileReject L R x y)
    (uniformRejectionRate S) (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hm : 0 ≤ min ((L x).weight a) ((R y).weight a) /
      (1 + totalVariation (L x).weight (R y).weight) :=
    div_nonneg (le_min ((L x).nonnegative a) ((R y).nonnegative a)) (by linarith)
  have hsurv :
      min ((L x).weight a) ((R y).weight a) /
          (1 + totalVariation (L x).weight (R y).weight) *
          (1 - uniformRejectionRate S ^ n) ≤
        min ((L x).weight a) ((R y).weight a) /
          (1 + totalVariation (L x).weight (R y).weight) *
          (1 - sharedProfileReject L R x y ^ n) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  refine hsurv.trans ?_
  simpa only [sharedProfileReject, sharedProfileLeft, sharedProfileRight] using
    rectangle_label_diagonal_bound (sharedProfileThresholds L R)
      (L x).weight (R y).weight fallback a
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))
      (L x).normalized (R y).normalized n

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end DFVSGames.Foundations.CorrelatedSampling


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem totalVariation_le_one (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ≤ 1 := by
  have hpoint : ∀ a, |p a - q a| ≤ p a + q a := by
    intro a
    rw [abs_le]
    constructor <;> linarith [hp.1 a, hq.1 a]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hsum
  dsimp [totalVariation]
  linarith

theorem le_binaryLog_of_le_log {r x : ℝ} (hr : 0 ≤ r) (h : r ≤ Real.log x) :
    r ≤ Real.log x / Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_one : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    exact ht
  apply (le_div_iff₀ htwo).2
  exact (mul_le_mul_of_nonneg_left htwo_one hr).trans (by simpa using h)

theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end DFVSGames.Foundations.Information

end OAI
