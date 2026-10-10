import OAI.Analysis.FiniteFactor.Sampling.SecondInterval

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The two closed intervals representing a positive superlevel of the
second-oriented tested reciprocal. Endpoint changes are dealt with separately. -/
def samplingSecondLevelLeft (h α a c s r : ℝ) : Set ℝ :=
  Set.Icc (max 0 (max (s-(1-α)) (s-c)))
    (min (min (min (samplingSecondLength h s) (min (s-α) (s-a))) (s-1/2)) (s-1+1/(h*r)))

def samplingSecondLevelRight (h α a c s r : ℝ) : Set ℝ :=
  Set.Icc (max (max (max 0 (max (s-(1-α)) (s-c))) (s-1/2)) (s-1/(h*r)))
    (min (samplingSecondLength h s) (min (s-α) (s-a)))

/-- A reciprocal superlevel is the union of two endpoint intervals. -/
theorem sampling_reciprocal_level (h r z : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hz : 0 < z) (hz1 : z < 1) :
    r ≤ 1/(h*samplingDistance z) ↔
      (z ≤ 1/2 ∧ z ≤ 1/(h*r)) ∨ (1/2 ≤ z ∧ 1-z ≤ 1/(h*r)) := by
  have hd : 0 < samplingDistance z := lt_min hz (by linarith)
  have hd' : 0 < h*samplingDistance z := mul_pos hh hd
  have hhr : 0 < h*r := mul_pos hh hr
  rw [le_div_iff₀ hd']
  by_cases hc : z ≤ 1/2
  · have he : samplingDistance z = z := min_eq_left (by linarith)
    rw [he]
    constructor
    · intro ha
      exact Or.inl ⟨hc,(le_div_iff₀ hhr).mpr (by nlinarith)⟩
    · rintro (ha|ha)
      · have hb := (le_div_iff₀ hhr).mp ha.2; nlinarith
      · have hb := (le_div_iff₀ hhr).mp ha.2
        have heq : z = 1/2 := le_antisymm hc ha.1
        rw [heq] at *
        nlinarith
  · have he : samplingDistance z = 1-z := min_eq_right (by linarith)
    rw [he]
    constructor
    · intro ha
      exact Or.inr ⟨by linarith,(le_div_iff₀ hhr).mpr (by nlinarith)⟩
    · rintro (ha|ha)
      · exact (hc ha.1).elim
      · have hb := (le_div_iff₀ hhr).mp ha.2; nlinarith

/-- Away from three possible jumps, the exact level indicator is the sum of
two closed-interval indicators. No variation theorem is assumed. -/
theorem samplingTestedSecond_level_intervals (h α : ℝ) (G : Set ℝ) (a c s r t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hr : 0 < r) (hsG : s ∈ G)
    (ht0 : t ≠ 0) (htL : t ≠ samplingSecondLength h s) (htmid : t ≠ s-1/2) :
    (if r ≤ samplingTestedSecondWeight h α (Set.Icc a c) G s t then (1 : ℝ) else 0) =
      (samplingSecondLevelLeft h α a c s r).indicator (fun _ => (1 : ℝ)) t +
      (samplingSecondLevelRight h α a c s r).indicator (fun _ => (1 : ℝ)) t := by
  rw [samplingTestedSecondWeight_interval h α G a c s t hh hh1 hα hs ht]
  have hsupport : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a)) ↔
      0 ≤ t ∧ t ≤ samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α ∧
        a ≤ s-t ∧ s-t ≤ c := by
    simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨h1,h2⟩; rcases h1 with ⟨h1,h1'⟩; rcases h2 with ⟨⟨h2,h3⟩,h4,h5⟩
      exact ⟨h1.le,h1'.le,by linarith,by linarith,by linarith,by linarith⟩
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm ht0),lt_of_le_of_ne h2 htL⟩,
        ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩⟩
  by_cases hc : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a))
  · have hz := hsupport.mp hc
    rw [Set.indicator_of_mem hc,ite_eq_left hsG]
    simp only [sampling_reciprocal_level h r (s-t) hh hr (hα.trans_le hz.2.2.1) (by linarith [hz.2.2.2.1])]
    simp only [samplingSecondLevelLeft,samplingSecondLevelRight,Set.indicator,
      Set.mem_Icc,max_le_iff,le_min_iff]
    have hm : s-t ≠ (1/2 : ℝ) := by intro he; apply htmid; linarith
    split_ifs <;> simp_all <;> grind
  · have hn := (not_congr hsupport).mp hc
    rw [Set.indicator_of_notMem hc,ite_eq_right (by linarith : ¬ r ≤ (0 : ℝ))]
    simp only [samplingSecondLevelLeft,samplingSecondLevelRight,Set.indicator,
      Set.mem_Icc,max_le_iff,le_min_iff]
    split_ifs <;> simp_all <;> grind

end
end FiniteFactor

end OAI
