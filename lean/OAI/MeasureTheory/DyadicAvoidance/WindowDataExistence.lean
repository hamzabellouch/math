import OAI.MeasureTheory.DyadicAvoidance.WindowData
import OAI.MeasureTheory.DyadicAvoidance.PreorderIndex
import OAI.MeasureTheory.DyadicAvoidance.TreeSpanBridge

namespace OAI

noncomputable section

namespace Problem310.WindowConstruction

open TreePreorder TreePreorderRank WindowPlacement
open scoped BigOperators

/-- Actual window lengths, in the finite tree preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  TreeSpanBridge.weights q d (WindowRecursion.length q g r₀)

def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ := WindowPlacement.lengthAt (lengths q d g r₀)

lemma lengthAt_edgeRank {q d g r₀ : ℕ} {P : List (Fin q)}
    (hP : ValidWindowEdge d P) :
    lengthAt q d g r₀ (edgeRank d P) = WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  have hm := (mem_edgePaths_iff q d P).mpr hP
  rw [PreorderIndex.edgeRank_eq_idxOf hm]
  exact WindowPlacement.lengthAt_map_idxOf _ hm

lemma length_preorderLengths (q g r₀ h : ℕ) :
    (WindowSpanSum.preorderLengths q g r₀ h).length = edgeCount q h := by
  rw [← TreeSpanBridge.weights_eq_preorderLengths q g r₀ h]
  simp [TreeSpanBridge.weights]

/-- Every descendant endpoint lies within twice the incoming window length. -/
theorem descendant_endpoint_bound {q d g r₀ : ℕ} (hq : 1 ≤ q)
    {P Q : List (Fin q)} (hP : ValidWindowEdge d P) (hQ : ValidWindowEdge d Q)
    (hpref : P.IsPrefix Q) :
    finish (lengthAt q d g r₀) g (edgeRank d Q) + 1 ≤
      start (lengthAt q d g r₀) g (edgeRank d P) +
        2 * WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  obtain ⟨pre, post, hL, hpre⟩ :=
    TreeSpanBridge.weighted_child_decomposition q g r₀ d P hP.1 hP.2
  have hmem := (mem_edgePaths_iff q d P).mpr hP
  have hpre' : pre.length = edgeRank d P := by
    rw [PreorderIndex.edgeRank_eq_idxOf hmem]
    exact hpre
  have hheight : d + 1 - P.length = (d - P.length) + 1 := by
    have hlen := hP.2
    omega
  let block := WindowRecursion.length q g r₀ (d + 1 - P.length) ::
    WindowSpanSum.preorderLengths q g r₀ (d - P.length)
  have hcard : block.length = edgeCount q (d - P.length) + 1 := by
    simp [block, length_preorderLengths]
  have hsum := WindowPlacement.sum_lengthAt_segment pre block post g
  have hL' : lengths q d g r₀ = pre ++ block ++ post := hL
  rw [← hL', hcard, hpre'] at hsum
  have hbudget :
      (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
        (lengthAt q d g r₀ (edgeRank d P + k) + g)) ≤
      2 * WindowRecursion.length q g r₀ (d + 1 - P.length) + g := by
    change (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
      (WindowPlacement.lengthAt (lengths q d g r₀) (edgeRank d P + k) + g)) ≤ _
    rw [hsum]
    change WindowSpanSum.paddedSum g block ≤ _
    dsimp [block]
    rw [hheight]
    exact WindowSpanSum.childBlock_budget q g r₀ (d - P.length) hq
  have hend := WindowPlacement.block_endpoint_le hbudget
  have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
  rw [PreorderIndex.size_eq_one_add_edgeCount] at hr
  have hle : edgeRank d Q ≤ edgeRank d P + edgeCount q (d - P.length) := by omega
  have hm := WindowPlacement.finish_mono (lengthAt q d g r₀) g hle
  omega

/-- The complete deterministic windows exist with any prescribed positive
uniform threshold and gap. -/
def windowData (q d g r₀ : ℕ) (hq : 1 ≤ q) (hr₀ : 1 ≤ r₀) :
    WindowData q d g r₀ where
  r := WindowRecursion.length q g r₀
  a P := start (lengthAt q d g r₀) g (edgeRank d P)
  b P := finish (lengthAt q d g r₀) g (edgeRank d P)
  bstar P := start (lengthAt q d g r₀) g (edgeRank d P) +
    2 * WindowRecursion.length q g r₀ (d + 1 - P.length) - 1
  length_pos P hP := hr₀.trans (WindowRecursion.threshold_le_length _ _ _ _)
  length_threshold P hP := WindowRecursion.threshold_le_length _ _ _ _
  start_three P hP := WindowPlacement.three_le_start _ _ _
  endpoint P hP := by
    rw [WindowPlacement.finish_add_one, lengthAt_edgeRank hP]
  gap_prefix P Q hP hQ hpref hne := by
    apply WindowPlacement.gap_of_lt
    have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
    apply lt_of_le_of_ne hr.1
    intro heq
    exact hne (edgeRank_injective_on hP.2 hQ.2 hP.1 hQ.1 heq)
  gap_sibling P i j tail hij hP hQ := by
    apply WindowPlacement.gap_of_lt
    exact edgeRank_sibling_descendants_lt (p := []) hij hP.2 hQ.2
  descendant_bounds P Q hP hQ hpref := by
    constructor
    · apply WindowPlacement.finish_mono
      exact ((isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref).1
    · have hb := descendant_endpoint_bound (g := g) (r₀ := r₀) hq hP hQ hpref
      omega
  padding P hP := by
    have hstart := WindowPlacement.three_le_start (lengthAt q d g r₀) g (edgeRank d P)
    omega

theorem exists_windowData (q d g r₀ : ℕ) (hq : 1 ≤ q) (hr₀ : 1 ≤ r₀) :
    Nonempty (WindowData q d g r₀) := ⟨windowData q d g r₀ hq hr₀⟩

end Problem310.WindowConstruction

end

end OAI
