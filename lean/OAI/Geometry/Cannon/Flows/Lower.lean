import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
open Set Metric

namespace CannonNode

def lower {X : Type*} [MetricSpace X] (f : X → ℝ) (y : X) (r : ℝ) : ℝ :=
  sInf (f '' closedBall y r)

def upper {X : Type*} [MetricSpace X] (f : X → ℝ) (y : X) (r : ℝ) : ℝ :=
  sSup (f '' closedBall y r)

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma ball_range {f : X → ℝ} {y : X} {r : ℝ}
    (hf : ContinuousOn f (closedBall y r)) {z : X} (hz : z ∈ closedBall y r) :
    lower f y r ≤ f z ∧ f z ≤ upper f y r := by
  have hc := (isCompact_closedBall y r).image_of_continuousOn hf
  exact ⟨csInf_le hc.bddBelow (mem_image_of_mem f hz),
    le_csSup hc.bddAbove (mem_image_of_mem f hz)⟩

lemma ball_extrema {f : X → ℝ} {y : X} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall y r)) :
    (∃ z ∈ closedBall y r, f z = lower f y r) ∧
    (∃ z ∈ closedBall y r, f z = upper f y r) := by
  have hc := (isCompact_closedBall y r).image_of_continuousOn hf
  have hne : (f '' closedBall y r).Nonempty := ⟨f y,y,mem_closedBall_self hr,rfl⟩
  exact ⟨hc.sInf_mem hne,hc.sSup_mem hne⟩

lemma lower_le_upper {f : X → ℝ} {y : X} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall y r)) : lower f y r ≤ upper f y r :=
  (ball_range hf (mem_closedBall_self hr)).1.trans (ball_range hf (mem_closedBall_self hr)).2

lemma ball_range_mono {f : X → ℝ} {y : X} {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hf : ContinuousOn f (closedBall y s)) :
    lower f y s ≤ lower f y r ∧ upper f y r ≤ upper f y s := by
  have hsub : closedBall y r ⊆ closedBall y s := closedBall_subset_closedBall hrs
  obtain ⟨⟨z,hz,hzv⟩,⟨w,hw,hwv⟩⟩ := ball_extrema hr (hf.mono hsub)
  exact ⟨hzv ▸ (ball_range hf (hsub hz)).1,hwv ▸ (ball_range hf (hsub hw)).2⟩

def childLower (a l : ℝ) : ℝ := max a l

def childUpper (b u : ℝ) : ℝ := min b u

def fraction (a b l u : ℝ) : ℝ := max 0 (childUpper b u-childLower a l)/(b-a)

lemma fraction_nonneg {a b l u : ℝ} (hab : a < b) : 0 ≤ fraction a b l u :=
  div_nonneg (le_max_left _ _) (sub_pos.mpr hab).le

lemma fraction_le_one {a b l u : ℝ} (hab : a < b) : fraction a b l u ≤ 1 := by
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  dsimp only [childUpper,childLower]
  have hu := min_le_left b u
  have hl := le_max_left a l
  change max 0 (min b u-max a l) ≤ 1*(b-a)
  exact max_le (by linarith only [hab]) (by linarith only [hu,hl])

lemma fraction_pos_iff {a b l u : ℝ} (hab : a < b) :
    0 < fraction a b l u ↔ childLower a l < childUpper b u := by
  rw [fraction,div_pos_iff_of_pos_right (sub_pos.mpr hab),lt_max_iff]
  simp only [lt_self_iff_false,false_or,sub_pos]

lemma child_nested {a b l u : ℝ} :
    Ioo (childLower a l) (childUpper b u) = Ioo a b ∩ Ioo l u := by
  ext t
  simp only [childLower,childUpper,mem_Ioo,mem_inter_iff,max_lt_iff,lt_min_iff]
  tauto

lemma positive_child_length {a b l u : ℝ} (hab : a < b)
    (hpos : 0 < fraction a b l u) :
    childUpper b u-childLower a l = (b-a)*fraction a b l u := by
  have hh := (fraction_pos_iff hab).mp hpos
  rw [fraction,max_eq_right (sub_nonneg.mpr hh.le)]
  field_simp [(sub_pos.mpr hab).ne']

end CannonNode

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
