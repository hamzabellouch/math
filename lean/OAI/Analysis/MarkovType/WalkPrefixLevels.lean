import OAI.Analysis.MarkovType.WalkLabels
import OAI.Analysis.MarkovType.WalkTransport
import OAI.Analysis.MarkovType.TwoLevels

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def rawChartWalkSum {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) : C00 :=
  ∑ i : Fin w.length, rawWalkLabel (C i.castSucc) (w.get i) (C i.succ)

theorem rawChartWalkSum_supportedBelow {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) :
    C00.SupportedBelow (rawChartWalkSum w C) B := by
  intro k hk
  rw [rawChartWalkSum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ =>
    rawWalkLabel_supportedBelow (C i.castSucc) (C i.succ) (w.get i) k hk

theorem rawChartWalkSum_prefix_bound {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) :
    prefixCut (rawChartWalkSum w C) B = 0 := by
  rw [rawChartWalkSum, prefixCut_finset_sum]
  exact Finset.sum_eq_zero fun i _ =>
    rawWalkLabel_prefix_bound (C i.castSucc) (C i.succ) (w.get i)

theorem rawChartWalkSum_prefix_cocycle {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) (y₀ : ℝ)
    (hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val y₀ ∈ walkLandmarks n)
    (hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val y₀ ∧
        pullbackPoint w k.val y₀ < (walkWindowLength n : ℝ))
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ)) :
    prefixCut (rawChartWalkSum w C)
      (chartCut (C 0) ⟨pullbackPoint w 0 y₀, hmem 0⟩) =
        (wordCocycle w y₀ : ℝ) := by
  rw [rawChartWalkSum, prefixCut_finset_sum, wordCocycle_eq_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hrank := pullbackPoint_good_path_cut w C y₀ hmem hgood i.castSucc
  rw [← hrank]
  exact rawWalkLabel_prefix_eq_chi (C i.castSucc) (C i.succ) (w.get i)
    ⟨pullbackPoint w i.val y₀, hmem i.castSucc⟩
    ⟨pullbackPoint w (i.val + 1) y₀, hmem i.succ⟩
    (hgood i) (letterOrderIso_pullbackPoint_succ w i y₀)
    (hwindow i.castSucc).1 (hwindow i.castSucc).2
    (hwindow i.succ).1 (hwindow i.succ).2

def walkIntegerPoint {n : ℕ} (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) : ↥(walkLandmarks n) :=
  ⟨(j : ℝ), sampled_integer_mem_walkLandmarks j hjlo hjhi⟩

def walkFractionPoint {n : ℕ} (hn : 0 < n) (w : List Letter)
    (hw : w.length ≤ n) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) : ↥(walkLandmarks n) :=
  ⟨walkOrbitFraction w + (j : ℝ), by
    simpa only [pullbackPoint_zero] using
      pullbackPoint_fraction_mem hn w hw 0 j hjlo hjhi⟩

theorem rawChartWalkSum_lower_level {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (j : ℤ) (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    prefixCut (rawChartWalkSum w C) (chartCut (C 0) (walkIntegerPoint j hjlo hjhi)) =
      -(negativeCount (reduceWord w) : ℝ) := by
  have hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val (j : ℝ) ∈ walkLandmarks n :=
    fun k => pullbackPoint_integer_mem w hw k.val j hjlo hjhi
  have hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val (j : ℝ) ∧
        pullbackPoint w k.val (j : ℝ) < (walkWindowLength n : ℝ) :=
    fun k => pullbackPoint_integer_window hn w hw k.val j hjlo hjhi
  have h := rawChartWalkSum_prefix_cocycle w C (j : ℝ) hmem hwindow hgood
  rw [wordCocycle_int] at h
  simpa only [pullbackPoint_zero, walkIntegerPoint, Int.cast_neg, Int.cast_natCast] using h

theorem rawChartWalkSum_upper_level {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (hne : reduceWord w ≠ [])
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ))
    (j : ℤ) (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    prefixCut (rawChartWalkSum w C)
      (chartCut (C 0) (walkFractionPoint hn w hw j hjlo hjhi)) =
        (positiveCount (reduceWord w) : ℝ) := by
  obtain ⟨hzlo, hzhi⟩ := walkOrbitFraction_bounds w
    (wordMap_zero_ne_int_of_reduceWord_ne_nil w hne)
  have hmem : ∀ k : Fin (w.length + 1),
      pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) ∈ walkLandmarks n :=
    fun k => pullbackPoint_fraction_mem hn w hw k.val j hjlo hjhi
  have hwindow : ∀ k : Fin (w.length + 1),
      0 < pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) ∧
        pullbackPoint w k.val (walkOrbitFraction w + (j : ℝ)) <
          (walkWindowLength n : ℝ) :=
    fun k => pullbackPoint_fraction_window hn w hw k.val j hjlo hjhi hzlo hzhi
  have h := rawChartWalkSum_prefix_cocycle w C
    (walkOrbitFraction w + (j : ℝ)) hmem hwindow hgood
  have hc : wordCocycle w (walkOrbitFraction w + (j : ℝ)) =
      (positiveCount (reduceWord w) : ℤ) := by
    rw [walkOrbitFraction_add_int, wordCocycle_upper]
  rw [hc] at h
  simpa only [pullbackPoint_zero, walkFractionPoint, Int.cast_natCast] using h

end MarkovSuperreflexivity

end

end OAI
