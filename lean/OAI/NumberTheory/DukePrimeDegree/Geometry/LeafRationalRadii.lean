import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafBoundedMaximal

namespace OAI

/-!
# Rational radii determine relative leaf bounds

Continuity from above for locally finite real measures lets the
measurable, countable family of rational-radius inequalities control
every positive real radius.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

lemma iInter_closedBall_of_antitone_tendsto (a : ℝ) (r : ℕ → ℝ)
    (hr : Antitone r) (hlim : Tendsto r atTop (𝓝 a)) :
    (⋂ m, closedBall (0 : ℝ) (r m)) = closedBall 0 a := by
  ext u
  simp only [mem_iInter, mem_closedBall]
  constructor
  · intro h
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall h)
  · intro h m
    exact h.trans (le_of_tendsto hlim (Filter.eventually_atTop.mpr
      ⟨m, fun n hn => hr hn⟩))

theorem relative_closedBall_bound_of_rational
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (E : Set ℝ) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hbound : ∀ q : ℚ, 0 < (q : ℝ) →
      ν (E ∩ closedBall 0 (q : ℝ)) ≤ c * ν (closedBall 0 (q : ℝ)))
    (r : ℝ) (hr : 0 < r) :
    ν (E ∩ closedBall 0 r) ≤ c * ν (closedBall 0 r) := by
  obtain ⟨q, hqanti, hqabove, hqlim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto
    (show Monotone (fun q : ℚ => (q : ℝ)) from fun a b h => by
      change (a : ℝ) ≤ (b : ℝ)
      exact_mod_cast h) r
  let R : ℕ → ℝ := fun m => q m
  have hanti : Antitone R := fun a b hab => by
    change (q b : ℝ) ≤ (q a : ℝ)
    exact_mod_cast hqanti.antitone hab
  have hi : (⋂ m, closedBall (0 : ℝ) (R m)) = closedBall 0 r :=
    iInter_closedBall_of_antitone_tendsto r R hanti hqlim
  have hlim : Tendsto (fun m => ν (closedBall 0 (R m))) atTop (𝓝 (ν (closedBall 0 r))) := by
    simpa only [hi, Function.comp_def] using tendsto_measure_iInter_atTop
      (μ := ν) (fun _ => isClosed_closedBall.measurableSet.nullMeasurableSet)
      (fun a b hab => closedBall_subset_closedBall (hanti hab))
      ⟨0, (isCompact_closedBall (0 : ℝ) (R 0)).measure_lt_top.ne⟩
  have hEi : (⋂ m, E ∩ closedBall (0 : ℝ) (R m)) = E ∩ closedBall 0 r := by
    rw [← inter_iInter, hi]
  have hElim : Tendsto (fun m => ν (E ∩ closedBall 0 (R m))) atTop
      (𝓝 (ν (E ∩ closedBall 0 r))) := by
    simpa only [hEi, Function.comp_def] using tendsto_measure_iInter_atTop
      (μ := ν) (fun _ => (hE.inter isClosed_closedBall.measurableSet).nullMeasurableSet)
      (fun a b hab => inter_subset_inter_right E (closedBall_subset_closedBall (hanti hab)))
      ⟨0, ne_top_of_le_ne_top (isCompact_closedBall (0 : ℝ) (R 0)).measure_lt_top.ne
        (measure_mono inter_subset_right)⟩
  apply le_of_tendsto_of_tendsto hElim ((ENNReal.continuous_const_mul hc).tendsto _ |>.comp hlim)
  exact Filter.Eventually.of_forall fun m => hbound (q m) (hr.trans (hqabove m))

end DukePrimeDegree

end

end OAI
