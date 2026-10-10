import OAI.Analysis.FiniteFactor.Sampling.Periodization

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Distance of a representative to the two ends of the unit interval. -/
def samplingDistance (s : ℝ) : ℝ := min s (1-s)

def samplingWeight (triangular : Bool) (h α s t : ℝ) : ℝ :=
  if triangular then
    if 0 < t ∧ t < 1-s then 1 else 0
  else
    if α ≤ samplingDistance s ∧ 0 < t ∧ t < h*samplingDistance s then
      1/(h*samplingDistance s)
    else 0

theorem samplingWeight_measurable (triangular : Bool) (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingWeight triangular h α p.1 p.2) := by
  cases triangular <;> unfold samplingWeight samplingDistance <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_le measurable_const (measurable_fst.min (measurable_const.sub measurable_fst))).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul (measurable_fst.min (measurable_const.sub measurable_fst)))))
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))) measurable_const measurable_const

theorem samplingWeight_bounds (triangular : Bool) (h α s t : ℝ) (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingWeight triangular h α s t ∧
      samplingWeight triangular h α s t ≤ max 1 (1/(h*α)) := by
  cases triangular
  · unfold samplingWeight
    simp only [Bool.false_eq_true,ite_false]
    split_ifs with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      exact ⟨by positivity, (one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hc.1 hh.le)).trans (le_max_right _ _)⟩
    · exact ⟨le_rfl,le_trans (by norm_num) (le_max_left _ _)⟩
  · unfold samplingWeight
    simp only [ite_true]
    split_ifs <;> constructor <;> first | positivity | exact le_max_left _ _

theorem samplingWeight_support (triangular : Bool) (h α s t : ℝ)
    (_hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (_hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    0 < t ∧ t < 1-s := by
  cases triangular
  · unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      have hd1 : samplingDistance s ≤ 1-s := min_le_right _ _
      exact ⟨hc.2.1, hc.2.2.trans_le ((by simpa using
        (mul_lt_mul_of_pos_right hh1 hd).le : h * samplingDistance s ≤ samplingDistance s).trans hd1)⟩
    · exact False.elim (hw rfl)
  · simpa only [samplingWeight,ite_true,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hw

/-- The positive weight already orders each prefix coordinate strictly,
with no wrap of the orbit endpoint. -/
theorem samplingWeight_orders (triangular : Bool) (h α s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    Int.fract (s+t) = s+t ∧ s < Int.fract (s+t) := by
  have ht := samplingWeight_support triangular h α s t hh hh1 hα hs hw
  have he := Int.fract_eq_self.mpr (show s+t ∈ Set.Ico (0 : ℝ) 1 from ⟨by linarith [hs.1],by linarith⟩)
  exact ⟨he,by rw [he]; linarith⟩

/-- In the second diagonal orientation the nonzero weight has no wrap and
the original coordinate is exactly s-t, as in the source calculation. -/
theorem samplingWeight_second_no_wrap (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hw : samplingWeight false h α (Int.fract (s-t)) t ≠ 0) :
    t < s ∧ Int.fract (s-t) = s-t := by
  have hsp := samplingWeight_support false h α (Int.fract (s-t)) t hh hh1 hα
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ hw
  have hcut : α ≤ samplingDistance (Int.fract (s-t)) := by
    unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · exact hc.1
    · exact False.elim (hw rfl)
  have hts : t < s := by
    by_contra hn
    have hle : s ≤ t := le_of_not_gt hn
    by_cases he : s = t
    · subst t
      simp [samplingDistance] at hcut
      linarith
    · have hst : s-t < 0 := sub_neg.mpr (lt_of_le_of_ne hle he)
      have hf : ⌊s-t⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr
        ⟨by norm_num; linarith [hs.1,ht.2],by norm_num; linarith⟩
      rw [Int.fract,hf] at hsp
      norm_num at hsp
      linarith [hsp.2,hs.1]
  exact ⟨hts,Int.fract_eq_self.mpr ⟨by linarith,by linarith [hs.2,ht.1]⟩⟩

/-- Exact first marginal of either untested one-coordinate weight. -/
theorem samplingWeight_first_integral (triangular : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight triangular h α s t ∂unitIntervalMeasure) =
      if triangular then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have hvol (L : ℝ) (hL : 0 ≤ L) (hL1 : L ≤ 1) :
      unitIntervalMeasure (Set.Ioo (0 : ℝ) L) = ENNReal.ofReal L := by
    unfold unitIntervalMeasure
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr (by
      intro t ht; exact ⟨ht.1.le,ht.2.trans_le hL1⟩),Real.volume_Ioo,sub_zero]
  cases triangular
  · simp only [Bool.false_eq_true,ite_false]
    by_cases hc : α ≤ samplingDistance s
    · have hd : 0 < samplingDistance s := hα.trans_le hc
      have hL : 0 < h*samplingDistance s := mul_pos hh hd
      have hL1 : h*samplingDistance s ≤ 1 := by
        have := min_le_right s (1-s)
        change samplingDistance s ≤ 1-s at this
        nlinarith [hs.1]
      have he : samplingWeight false h α s =
          (Set.Ioo 0 (h*samplingDistance s)).indicator (fun _ => 1/(h*samplingDistance s)) := by
        funext t
        simp [samplingWeight,hc,Set.indicator,Set.mem_Ioo]
      rw [he,integral_indicator measurableSet_Ioo]
      simp [hc,hvol (h*samplingDistance s) hL.le hL1,ENNReal.toReal_ofReal hL.le,measureReal_def]
      field_simp
    · have he : samplingWeight false h α s = fun _ => 0 := by funext t; simp [samplingWeight,hc]
      simp [he,hc]
  · simp only [ite_true]
    have he : samplingWeight true h α s = (Set.Ioo 0 (1-s)).indicator (fun _ => (1 : ℝ)) := by
      funext t
      simp [samplingWeight,Set.indicator,Set.mem_Ioo]
    rw [he,integral_indicator measurableSet_Ioo]
    simp [hvol (1-s) (by linarith [hs.2]) (by linarith [hs.1]),ENNReal.toReal_ofReal,show 0 ≤ 1-s by linarith [hs.2],measureReal_def]

end
end FiniteFactor

end OAI
