import OAI.Analysis.MarkovType.WalkPrefixLevels
import OAI.Analysis.MarkovType.InterleavedCuts

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def walkSampleInteger (n : ℕ) (i : Fin (walkWindowPairs n + 1)) : ℤ :=
  (walkWindowLeft n : ℤ) + (i.val : ℤ)

theorem walkSampleInteger_bounds (n : ℕ) (i : Fin (walkWindowPairs n + 1)) :
    (walkWindowLeft n : ℤ) ≤ walkSampleInteger n i ∧
      walkSampleInteger n i ≤ (walkWindowRight n : ℤ) := by
  have hi : (i.val : ℤ) ≤ (walkWindowPairs n : ℤ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hiz : (0 : ℤ) ≤ i.val := Int.natCast_nonneg _
  simp only [walkSampleInteger, walkWindowLeft, walkWindowRight, walkWindowPairs,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  constructor <;> omega

@[simp] theorem walkSampleInteger_succ (n : ℕ) (i : Fin (walkWindowPairs n)) :
    walkSampleInteger n i.succ = walkSampleInteger n i.castSucc + 1 := by
  simp [walkSampleInteger, Nat.cast_add, Nat.cast_one, add_assoc]

theorem walkSampleInteger_lt_length (n : ℕ) (i : Fin (walkWindowPairs n + 1)) :
    (walkSampleInteger n i : ℝ) < (walkWindowLength n : ℝ) := by
  have hhi : (walkSampleInteger n i : ℝ) ≤ (walkWindowRight n : ℝ) := by
    exact_mod_cast (walkSampleInteger_bounds n i).2
  have hlast : (walkWindowRight n : ℝ) < (walkWindowLength n : ℝ) := by
    exact_mod_cast walkWindowRight_lt_length n
  exact hhi.trans_lt hlast

theorem rawChartWalkSum_displacement (N : OrderedNorm) {n B : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (hne : reduceWord w ≠ [])
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B)
    (hgood : ∀ i : Fin w.length,
      Chart.Good (letterOrderIso (w.get i)) (C i.castSucc) (C i.succ)) :
    (reducedLength w : ℝ) * N.alternatingNorm (walkWindowLength n) ≤
      6 * N (rawChartWalkSum w C) := by
  let M := walkWindowPairs n
  let r : Fin (M + 1) → ℕ := fun i => chartCut (C 0)
    (walkIntegerPoint (walkSampleInteger n i)
      (walkSampleInteger_bounds n i).1 (walkSampleInteger_bounds n i).2)
  let t : Fin M → ℕ := fun i => chartCut (C 0)
    (walkFractionPoint hn w hw (walkSampleInteger n i.castSucc)
      (walkSampleInteger_bounds n i.castSucc).1
      (walkSampleInteger_bounds n i.castSucc).2)
  obtain ⟨hzlo, hzhi⟩ := walkOrbitFraction_bounds w
    (wordMap_zero_ne_int_of_reduceWord_ne_nil w hne)
  have hr0 : 0 < r 0 := chartCut_pos (C 0) _
  have hrt : ∀ i : Fin M, r i.castSucc < t i ∧ t i < r i.succ := by
    intro i
    constructor
    · apply chartCut_lt_of_lt (C 0)
      change (walkSampleInteger n i.castSucc : ℝ) <
        walkOrbitFraction w + (walkSampleInteger n i.castSucc : ℝ)
      linarith
    · apply chartCut_lt_of_lt (C 0)
      change walkOrbitFraction w + (walkSampleInteger n i.castSucc : ℝ) <
        (walkSampleInteger n i.succ : ℝ)
      rw [walkSampleInteger_succ, Int.cast_add, Int.cast_one]
      linarith
  have hrB : r (Fin.last M) < B := by
    apply chartCut_lt_bound_of_lt (C 0)
      (y := ⟨(walkWindowLength n : ℝ), length_mem_walkLandmarks n⟩)
    exact walkSampleInteger_lt_length n (Fin.last M)
  let U : ℝ := positiveCount (reduceWord w)
  let V : ℝ := -(negativeCount (reduceWord w) : ℝ)
  have hgap : U - V = (reducedLength w : ℝ) := by
    dsimp [U, V, reducedLength]
    rw [sub_neg_eq_add, ← Nat.cast_add, positiveCount_add_negativeCount]
  have hr : ∀ i, prefixCut (rawChartWalkSum w C) (r i) = V := by
    intro i
    exact rawChartWalkSum_lower_level hn w hw C hgood
      (walkSampleInteger n i) (walkSampleInteger_bounds n i).1
      (walkSampleInteger_bounds n i).2
  have ht : ∀ i, prefixCut (rawChartWalkSum w C) (t i) = U := by
    intro i
    exact rawChartWalkSum_upper_level hn w hw hne C hgood
      (walkSampleInteger n i.castSucc) (walkSampleInteger_bounds n i.castSucc).1
      (walkSampleInteger_bounds n i.castSucc).2
  have h := N.alternatingNorm_six_le_of_interleaved M B r t hr0 hrt hrB
    (rawChartWalkSum w C) (rawChartWalkSum_supportedBelow w C)
    (rawChartWalkSum_prefix_bound w C) (reducedLength w : ℝ) U V
    (Nat.cast_nonneg _) hgap hr ht
  simpa only [walkWindowLength_eq_twice_pairs, M] using h

end MarkovSuperreflexivity

end

end OAI
