import OAI.NumberTheory.Jacobsthal.Probability.EvenThresholdEvent

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdGeometry
open Set MeasureTheory FinitePathGeometry ErdosEvenThreshold

noncomputable def normalizedSlack (R t : ℝ) : ℝ := thresholdSlack R t/R

theorem normalizedSlack_eq_min {R t : ℝ} (hR : 0 < R) (ht : 0 < t+1) :
    normalizedSlack R t=min ((t-2)/(t+1)) ((t-1)/(t+1)-2/R) := by
  rw [normalizedSlack,thresholdSlack,← min_sub_sub_left,← min_div_div_right hR.le]
  congr 1
  · unfold nextGap nextExponent
    field_simp [hR.ne',ht.ne']
  · unfold nextGap nextExponent
    field_simp [hR.ne',ht.ne']
    ring

noncomputable def thickStrip (R delta : ℝ) : Set ℝ :=
  {t | 2 ≤ t ∧ t ≤ 5 ∧ |normalizedSlack R t| ≤ delta}

theorem thickStrip_cover {R delta t : ℝ} (hR : 3 ≤ R) (ht : t ∈ thickStrip R delta) :
    t ∈ Icc 2 (2+6*delta) ∪ Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta) := by
  obtain ⟨ht2,ht5,hslack⟩ := ht
  have hRp : 0 < R := by linarith
  have hRm : 0 < R-2 := by linarith
  have htp : 0 < t+1 := by linarith
  have hd : 0 ≤ delta := (abs_nonneg _).trans hslack
  rw [normalizedSlack_eq_min hRp htp] at hslack
  by_cases hbranch : (t-2)/(t+1) ≤ (t-1)/(t+1)-2/R
  · rw [min_eq_left hbranch] at hslack
    have hh := (div_le_iff₀ htp).mp ((le_abs_self _).trans hslack)
    exact Or.inl ⟨ht2,by nlinarith⟩
  · rw [min_eq_right (le_of_not_ge hbranch)] at hslack
    have he : t-(R+2)/(R-2)=((t-1)/(t+1)-2/R)*((t+1)*R/(R-2)) := by
      field_simp [hRp.ne',hRm.ne',htp.ne']
      ring
    have hfac0 : 0 ≤ (t+1)*R/(R-2) := by positivity
    have hfac : (t+1)*R/(R-2) ≤ 18 := by
      apply (div_le_iff₀ hRm).mpr
      nlinarith
    have habs : |t-(R+2)/(R-2)| ≤ 18*delta := by
      rw [he,abs_mul,abs_of_nonneg hfac0]
      nlinarith [mul_le_mul hslack hfac hfac0 hd]
    exact Or.inr ⟨by linarith [(abs_le.mp habs).1],by linarith [(abs_le.mp habs).2]⟩

theorem thickStrip_measurable (R delta : ℝ) : MeasurableSet (thickStrip R delta) := by
  have hs : Measurable (normalizedSlack R) := by
    unfold normalizedSlack thresholdSlack nextGap nextExponent
    fun_prop
  exact measurableSet_Ici.inter (measurableSet_Iic.inter (measurableSet_le hs.abs measurable_const))

theorem thickStrip_volume {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    volume (thickStrip R delta) ≤ ENNReal.ofReal (42*delta) := by
  calc
    _ ≤ volume (Icc 2 (2+6*delta) ∪ Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta)) :=
      measure_mono (fun _ ht => thickStrip_cover hR ht)
    _ ≤ volume (Icc 2 (2+6*delta))+volume (Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta)) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (6*delta)+ENNReal.ofReal (36*delta) := by
      rw [Real.volume_Icc,Real.volume_Icc]
      congr 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (42*delta) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
end NumberTheoryLean.TwoSidedThresholdGeometry

end

end Erdos970

end OAI
