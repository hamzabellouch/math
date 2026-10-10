import OAI.Analysis.FiniteFactor.Sampling.TestedSecondMoment

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

def samplingSecondLength (h s : ℝ) : ℝ := min (h*s/(1+h)) (h*(1-s)/(1-h))

theorem samplingSecondWeight_support_iff (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingSecondWeight h α s t ≠ 0 ↔
      0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α := by
  have hplus : 0 < 1+h := by linarith
  have hminus : 0 < 1-h := by linarith
  constructor
  · intro hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    have hc : α ≤ samplingDistance (s-t) ∧ 0 < t ∧ t < h*samplingDistance (s-t) := by
      unfold samplingSecondWeight samplingWeight at hw
      simp only [Bool.false_eq_true,ite_false,hf] at hw
      split_ifs at hw with hc
      · exact hc
      · exact False.elim (hw rfl)
    have hcut := le_min_iff.mp hc.1
    have hleft : t < h*(s-t) := hc.2.2.trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hh.le)
    have hright : t < h*(1-(s-t)) := hc.2.2.trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hh.le)
    refine ⟨hc.2.1,?_,hcut.1,by linarith [hcut.2]⟩
    unfold samplingSecondLength
    rw [lt_min_iff,lt_div_iff₀ hplus,lt_div_iff₀ hminus]
    constructor <;> nlinarith
  · rintro ⟨ht0,htL,hcut,hcut'⟩
    have hz : s-t ∈ Set.Ico (0 : ℝ) 1 := ⟨hα.le.trans hcut,by linarith⟩
    have hf := Int.fract_eq_self.mpr hz
    have hL := lt_min_iff.mp htL
    have hl := (lt_div_iff₀ hplus).mp hL.1
    have hr := (lt_div_iff₀ hminus).mp hL.2
    have htl : t < h*(s-t) := by nlinarith
    have htr : t < h*(1-(s-t)) := by nlinarith
    have hd : α ≤ samplingDistance (s-t) := le_min hcut (by linarith)
    have htd : t < h*samplingDistance (s-t) := by
      unfold samplingDistance
      rw [mul_min_of_nonneg _ _ hh.le]
      exact lt_min htl htr
    have hp : 0 < h*samplingDistance (s-t) := mul_pos hh (hα.trans_le hd)
    simp [samplingSecondWeight,samplingWeight,hf,hd,ht0,htd,(hα.trans_le hd).ne',hh.ne']

/-- Exact reciprocal on the actual second-oriented support. -/
theorem samplingSecondWeight_interval (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingSecondWeight h α s t =
      if 0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α
      then 1/(h*samplingDistance (s-t)) else 0 := by
  by_cases hw : samplingSecondWeight h α s t ≠ 0
  · have hc := (samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mp hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    rw [ite_eq_left hc]
    unfold samplingSecondWeight samplingWeight at *
    simp only [Bool.false_eq_true,ite_false,hf] at *
    split_ifs at * <;> simp_all
  · rw [not_ne_iff] at hw
    have hc : ¬ (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) := by
      intro hc
      exact ((samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mpr hc) hw
    rw [ite_eq_right hc,hw]

/-- The x-test intersects that support with a reflected interval, while the
y-test is constant in the phase variable. -/
theorem samplingTestedSecondWeight_interval (h α : ℝ) (G : Set ℝ) (a c s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedSecondWeight h α (Set.Icc a c) G s t =
      (Set.Ioo 0 (samplingSecondLength h s) ∩
        Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a))).indicator
        (fun t => if s ∈ G then 1/(h*samplingDistance (s-t)) else 0) t := by
  have heq : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a)) ↔
      (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) ∧ s-t ∈ Set.Icc a c := by
    simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨ht0,hL⟩
      exact ⟨⟨ht0.1,ht0.2,by linarith [hL.2.1],by linarith [hL.1.1]⟩,
        ⟨by linarith [hL.2.2],by linarith [hL.1.2]⟩⟩
    · rintro ⟨⟨ht0,hL,hcut,hcut'⟩,ha,hc⟩
      exact ⟨⟨ht0,hL⟩,⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩⟩
  by_cases hw : samplingSecondWeight h α s t ≠ 0
  · have hc := (samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mp hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    rw [samplingTestedSecondWeight,samplingSecondWeight_interval h α s t hh hh1 hα hs ht,
      ite_eq_left hc,hf]
    simp only [Set.indicator,heq,hc,true_and]
    split_ifs <;> simp_all
  · have hc : ¬ (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) := by
      intro hc
      exact hw ((samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mpr hc)
    have hz := not_ne_iff.mp hw
    simp only [samplingTestedSecondWeight,hz,ite_self,Set.indicator,heq,hc,false_and,ite_false]

end
end FiniteFactor

end OAI
