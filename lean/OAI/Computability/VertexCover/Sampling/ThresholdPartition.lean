import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                          
section

namespace UniqueGames.Foundations.CorrelatedSampling

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

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
