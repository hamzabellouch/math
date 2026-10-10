import OAI.Probability.FreeIsing.Trees.InwardCutChannels
import OAI.Probability.FreeIsing.Trees.InwardCutFields

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.InwardCutChannels

open PathSideBranches CutContinuationChannels ConnectedHull

def inwardContinuationProduct {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta
    (cutInwardGaussianField μ t (appendCutContinuation p w).1 (k + 1) i z) ^ 2

def inwardContinuationAverage {d k : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (L : ℕ) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  (∑ w : ReducedTail (cutLastColor p) L, inwardContinuationProduct μ t theta p w s z) /
    (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ)

theorem inwardContinuationProduct_Ico_eq_range {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    inwardContinuationProduct μ t theta p w (Finset.Ico (k + 1) (k + 1 + L)) z =
      ∏ j ∈ Finset.range L, responseAttenuation theta
        (cutInwardGaussianField μ t (appendCutContinuation p w).1
          (k + 1) (k + 1 + j) z) ^ 2 := by
  simp only [inwardContinuationProduct, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel_left]

theorem takeVertex_appendCutContinuation {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    takeVertex (appendCutContinuation p w).1 (k + 1) = p.1 := by
  apply Subtype.ext
  simp [takeVertex, appendCutContinuation, p.2]

private theorem inward_region_subset_cut {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (i : ℕ) :
    cone (takeVertex (appendCutContinuation p w).1 (k + 1)) \
        cone (takeVertex (appendCutContinuation p w).1 (i + 1)) ⊆ cone p.1 := by
  rw [takeVertex_appendCutContinuation]
  exact Set.sdiff_subset

private theorem reducedTail_nonempty {d k : ℕ} (hd : 2 ≤ d)
    (p : TreeShell d (k + 1)) (L : ℕ) :
    Nonempty (ReducedTail (cutLastColor p) L) := by
  apply Fintype.card_pos_iff.mp
  rw [card_reducedTail]
  exact pow_pos (by omega : 0 < d - 1) L

theorem exists_inwardContinuationAverage_channel {d k : ℕ} (hd : 2 ≤ d)
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (p : TreeShell d (k + 1)) (L : ℕ) (s : Finset ℕ) :
    ∃ g : ConeSample ℝ p.1 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, inwardContinuationAverage μ t theta p L s z = g (globalCone p.1 z) := by
  let := reducedTail_nonempty hd p L
  have hF : Measurable (Function.uncurry (fun a x => (t : ℝ) * spinSign a + x)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  exact exists_regionAverage_channel
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hF hθ p.1
    (fun w i => cone (takeVertex (appendCutContinuation p w).1 (k + 1)) \
      cone (takeVertex (appendCutContinuation p w).1 (i + 1)))
    (fun w i => takeVertex (appendCutContinuation p w).1 i)
    (fun _ => s) (inward_region_subset_cut p)

theorem integral_inwardContinuationAverage_le {d k : ℕ} (hd : 2 ≤ d)
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (p : TreeShell d (k + 1)) (L : ℕ) (s : Finset ℕ)
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)))
    [IsProbabilityMeasure P] {m : ℝ}
    (hmean : ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, inwardContinuationProduct μ t theta p w s z ∂P) ≤ m) :
    (∫ z, inwardContinuationAverage μ t theta p L s z ∂P) ≤ m := by
  let := reducedTail_nonempty hd p L
  have hF : Measurable (Function.uncurry (fun a x => (t : ℝ) * spinSign a + x)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  exact integral_regionAverage_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hF hθ p.1
    (fun w i => cone (takeVertex (appendCutContinuation p w).1 (k + 1)) \
      cone (takeVertex (appendCutContinuation p w).1 (i + 1)))
    (fun w i => takeVertex (appendCutContinuation p w).1 i)
    (fun _ => s) (inward_region_subset_cut p) P hmean

end Problem367.InwardCutChannels

end

end OAI
