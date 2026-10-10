import OAI.NumberTheory.Jacobsthal.Partitions.EvenThresholdGeometry

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set MeasureTheory NumberTheoryLean.FinitePathGeometry

theorem cover_width_bound {R d : ℝ} (hR : 4 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ firstUpper R d-2 ∧ 0 ≤ secondUpper R d-secondLower R ∧
      (firstUpper R d-2)+(secondUpper R d-secondLower R) ≤ 20*d/R := by
  have hR0 : 0 < R := by linarith
  have hA : 0 < R-2 := by linarith
  have hB : 0 < R-2-d := by linarith
  have he : secondUpper R d-secondLower R=2*R*d/((R-2)*(R-2-d)) := by
    unfold secondUpper secondLower
    field_simp
    ring
  have hprod : R^2/8 ≤ (R-2)*(R-2-d) := by
    have ha : R/2 ≤ R-2 := by linarith
    have hb : R/4 ≤ R-2-d := by linarith
    have hh := mul_le_mul ha hb (by linarith : 0 ≤ R/4) hA.le
    nlinarith only [hh]
  have hlength : secondUpper R d-secondLower R ≤ 16*d/R := by
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hA hB) hR0).mpr
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 16*d by positivity)
    nlinarith only [hh]
  refine ⟨?_,?_,?_⟩
  · unfold firstUpper
    have hh : 0 ≤ 4*d/R := by positivity
    linarith
  · rw [he]
    positivity
  · have hf : firstUpper R d-2=4*d/R := by unfold firstUpper; ring
    rw [hf]
    calc
      _ ≤ 4*d/R+16*d/R := add_le_add le_rfl hlength
      _ = _ := by ring

theorem thresholdStrip_measurable (R d : ℝ) : MeasurableSet (thresholdStrip R d) := by
  have hx : Measurable (fun t : ℝ => nextExponent R t) := by unfold nextExponent; fun_prop
  have hs : Measurable (thresholdSlack R) := by unfold thresholdSlack nextGap nextExponent; fun_prop
  exact measurableSet_Ici.inter ((measurableSet_lt measurable_const hx).inter
    ((measurableSet_le measurable_const hs).inter (measurableSet_le hs measurable_const)))

theorem thresholdStrip_empty {R d : ℝ} (hR : R ≤ 4) (hd1 : d ≤ 1) : thresholdStrip R d=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact (not_lt_of_ge hR) (strip_parameters hd1 ht).1

theorem thresholdStrip_volume {R d : ℝ} (_hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    volume (thresholdStrip R d) ≤ ENNReal.ofReal (20*d/R) := by
  by_cases hR4 : 4 < R
  · have hwidth := cover_width_bound hR4 hd0 hd1
    calc
      _ ≤ volume (Icc 2 (firstUpper R d) ∪ Icc (secondLower R) (secondUpper R d)) :=
        measure_mono (fun _ ht => strip_mem_cover hd0 hd1 ht)
      _ ≤ volume (Icc 2 (firstUpper R d))+volume (Icc (secondLower R) (secondUpper R d)) := measure_union_le _ _
      _ = ENNReal.ofReal ((firstUpper R d-2)+(secondUpper R d-secondLower R)) := by
        rw [Real.volume_Icc,Real.volume_Icc,ENNReal.ofReal_add hwidth.1 hwidth.2.1]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hwidth.2.2
  · rw [thresholdStrip_empty (le_of_not_gt hR4) hd1,measure_empty]
    exact bot_le

end ErdosEvenThreshold

end

end Erdos970

end OAI
