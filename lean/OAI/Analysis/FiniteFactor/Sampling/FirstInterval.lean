import OAI.Analysis.FiniteFactor.Sampling.TestedFirstMoment

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

def samplingFirstLength (b : Bool) (h s : ℝ) : ℝ :=
  if b then 1-s else h*samplingDistance s

def samplingFirstHeight (b : Bool) (h α s : ℝ) : ℝ :=
  if b then 1 else if α ≤ samplingDistance s then 1/(h*samplingDistance s) else 0

/-- The first-oriented weight is exactly a constant times one open interval. -/
theorem samplingWeight_first_interval (b : Bool) (h α s t : ℝ) :
    samplingWeight b h α s t =
      (Set.Ioo 0 (samplingFirstLength b h s)).indicator
        (fun _ => samplingFirstHeight b h α s) t := by
  cases b <;> unfold samplingWeight samplingFirstLength samplingFirstHeight <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Set.indicator,Set.mem_Ioo];
    split_ifs <;> simp_all

/-- Rational rectangle tests retain a single interval in the first orientation;
no bounded-variation theorem or independent pair density is assumed. -/
theorem samplingTestedFirstWeight_interval (b : Bool) (h α : ℝ) (E : Set ℝ) (a c s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstWeight b h α E (Set.Icc a c) s t =
      (Set.Ioo 0 (samplingFirstLength b h s) ∩ Set.Icc (a-s) (c-s)).indicator
        (fun _ => if s ∈ E then samplingFirstHeight b h α s else 0) t := by
  classical
  have he := samplingWeight_first_interval b h α s t
  by_cases ht : t ∈ Set.Ioo 0 (samplingFirstLength b h s)
  · rw [Set.indicator_of_mem ht] at he
    by_cases hc : samplingFirstHeight b h α s = 0
    · simp [samplingTestedFirstWeight,he,hc,Set.indicator]
    · have hw : samplingWeight b h α s t ≠ 0 := by rwa [he]
      have hf := (samplingWeight_orders b h α s t hh hh1 hα hs hw).1
      have heq : Int.fract (s+t) ∈ Set.Icc a c ↔ t ∈ Set.Icc (a-s) (c-s) := by
        rw [hf]
        simp only [Set.mem_Icc]
        constructor <;> intro H <;> constructor <;> linarith [H.1,H.2]
      simp only [samplingTestedFirstWeight,he,heq,Set.indicator,Set.mem_inter_iff,ht,true_and]
      split_ifs <;> simp_all
  · rw [Set.indicator_of_notMem ht] at he
    simp [samplingTestedFirstWeight,he,Set.indicator,ht]

/-- Closing the two support endpoints changes only those two points, even
when the tested interval is empty or degenerates to a singleton. -/
theorem samplingTestedFirstWeight_closed_interval (b : Bool) (h α : ℝ) (E : Set ℝ) (a c s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (ht0 : t ≠ 0) (htL : t ≠ samplingFirstLength b h s) :
    samplingTestedFirstWeight b h α E (Set.Icc a c) s t =
      (Set.Icc (max 0 (a-s)) (min (samplingFirstLength b h s) (c-s))).indicator
        (fun _ => if s ∈ E then samplingFirstHeight b h α s else 0) t := by
  rw [samplingTestedFirstWeight_interval b h α E a c s t hh hh1 hα hs]
  have heq : t ∈ Set.Ioo 0 (samplingFirstLength b h s) ∩ Set.Icc (a-s) (c-s) ↔
      t ∈ Set.Icc (max 0 (a-s)) (min (samplingFirstLength b h s) (c-s)) := by
    simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · intro H
      exact ⟨⟨H.1.1.le,H.2.1⟩,⟨H.1.2.le,H.2.2⟩⟩
    · intro H
      exact ⟨⟨lt_of_le_of_ne H.1.1 (Ne.symm ht0),lt_of_le_of_ne H.2.1 htL⟩,⟨H.1.2,H.2.2⟩⟩
  simp only [Set.indicator,heq]

/-- The exact interval representation under any atomless law, including Haar. -/
theorem samplingTestedFirstWeight_closed_interval_ae (μ : Measure ℝ) [NullSingletonClass μ]
    (b : Bool) (h α : ℝ) (E : Set ℝ) (a c s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstWeight b h α E (Set.Icc a c) s =ᵐ[μ]
      (Set.Icc (max 0 (a-s)) (min (samplingFirstLength b h s) (c-s))).indicator
        (fun _ => if s ∈ E then samplingFirstHeight b h α s else 0) := by
  filter_upwards [ae_iff.mpr (show μ {t | ¬t ≠ 0} = 0 by simp),
    ae_iff.mpr (show μ {t | ¬t ≠ samplingFirstLength b h s} = 0 by simp)] with t ht0 htL
  exact samplingTestedFirstWeight_closed_interval b h α E a c s t hh hh1 hα hs ht0 htL

end
end FiniteFactor

end OAI
