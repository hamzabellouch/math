import Mathlib
import OAI.Computability.MinUncut.Games.OuterQuestions

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

def thresholdSample {α : Type*} (mass : α → Nat) (proposals : List (α × Nat)) :
    Option α :=
  (firstAccepted (fun s => decide (s.2 < mass s.1)) proposals).map Prod.fst

theorem thresholdSample_agreement {α : Type*} (left right : α → Nat)
    (proposals : List (α × Nat)) (a : α) (height : Nat)
    (hfirst : firstAccepted
      (fun s => decide (s.2 < left s.1) || decide (s.2 < right s.1)) proposals =
      some (a, height))
    (hcommon : height < min (left a) (right a)) :
    thresholdSample left proposals = some a ∧
      thresholdSample right proposals = some a := by
  have h := first_union_common
    (fun s : α × Nat => decide (s.2 < left s.1))
    (fun s : α × Nat => decide (s.2 < right s.1)) proposals (a, height) hfirst
    (by simpa using (lt_min_iff.mp hcommon).1)
    (by simpa using (lt_min_iff.mp hcommon).2)
  simp [thresholdSample, h.1, h.2]

noncomputable section

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def overlapMass (p q : α → ℝ) : ℝ := ∑ a, min (p a) (q a)

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem overlapMass_nonneg (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) : 0 ≤ overlapMass p q := by
  exact Finset.sum_nonneg (fun a _ => le_min (hp a) (hq a))

private theorem min_abs_identity (x y : ℝ) : 2 * min x y + |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

private theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem overlapMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q = 1 - totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => min_abs_identity (p a) (q a))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold overlapMass totalVariation
  linarith

theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

theorem totalVariation_le_one (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    totalVariation p q ≤ 1 := by
  have h := overlapMass_nonneg p q hp hq
  rw [overlapMass_eq p q hpsum hqsum] at h
  linarith

theorem overlap_union_ratio (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q / unionMass p q =
      (1 - totalVariation p q) / (1 + totalVariation p q) := by
  rw [overlapMass_eq p q hp hq, unionMass_eq p q hp hq]

theorem overlap_union_ratio_lower_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - 2 * totalVariation p q ≤ overlapMass p q / unionMass p q := by
  rw [overlap_union_ratio p q hp hq]
  have htv := totalVariation_nonneg p q
  have hden : 0 < 1 + totalVariation p q := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (totalVariation p q)]

theorem first_union_disagreement_upper_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - overlapMass p q / unionMass p q ≤ 2 * totalVariation p q := by
  linarith [overlap_union_ratio_lower_bound p q hp hq]

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_nonneg (r : ℝ) (hr : 0 ≤ r) (n : Nat) :
    0 ≤ geometricMass r n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih => exact add_nonneg (by norm_num) (mul_nonneg hr ih)

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_nonneg (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (n : Nat) (output : Option σ) :
    0 ≤ firstHitWeight w accept n output := by
  induction n generalizing output with
  | zero => cases output <;> simp [firstHitWeight]
  | succ n ih =>
      have hr := eventMass_nonneg w (fun s => !(accept s)) hw
      cases output with
      | none => exact mul_nonneg hr (ih none)
      | some s =>
          apply add_nonneg
          · split <;> simp_all
          · exact mul_nonneg hr (ih (some s))

theorem firstHitWeight_none (w : σ → ℝ) (accept : σ → Bool) (n : Nat) :
    firstHitWeight w accept n none = eventMass w (fun s => !(accept s)) ^ n := by
  induction n with
  | zero => simp [firstHitWeight]
  | succ n ih => simp [firstHitWeight, ih, pow_succ, mul_comm]

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

theorem firstHitWeight_normalized (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) : ∑ output, firstHitWeight w accept n output = 1 := by
  rw [Fintype.sum_option, firstHitWeight_none]
  simp_rw [firstHitWeight_some]
  rw [← Finset.sum_mul]
  change eventMass w (fun s => !(accept s)) ^ n +
    eventMass w accept * geometricMass (eventMass w (fun s => !(accept s))) n = 1
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have ha : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
  rw [ha, hg]
  ring

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

theorem commonMass_le_acceptMass (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) :
    eventMass w (fun s => accept s && good s) ≤ eventMass w accept := by
  apply Finset.sum_le_sum
  intro s _
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, hw s]

theorem goodFirstMass_lower_bound (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (hw_sum : ∑ s, w s = 1)
    (ha : 0 < eventMass w accept) (n : Nat) :
    eventMass w (fun s => accept s && good s) / eventMass w accept -
        eventMass w (fun s => !(accept s)) ^ n ≤ goodFirstMass w accept good n := by
  rw [goodFirstMass_exact w accept good hw_sum (ne_of_gt ha) n]
  have hratio : eventMass w (fun s => accept s && good s) / eventMass w accept ≤ 1 := by
    apply (div_le_one ha).2
    exact commonMass_le_acceptMass w accept good hw
  have htail : 0 ≤ eventMass w (fun s => !(accept s)) ^ n :=
    pow_nonneg (eventMass_nonneg w (fun s => !(accept s)) hw) n
  nlinarith

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

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
