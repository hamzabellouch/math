import OAI.Probability.FreeIsing.Trees.CutContinuations
import OAI.Probability.FreeIsing.Trees.InwardCutFields

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367
open PathSideBranches

def gaussianInwardConeFactor {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (theta : ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) (v : TreeVertex d) : ℝ :=
  responseAttenuation theta
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z) ^ 2

theorem measurable_gaussianInwardConeFactor {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (v : TreeVertex d) :
    Measurable (fun z => gaussianInwardConeFactor μ t theta z v) :=
  ((continuous_responseAttenuation hθ).measurable.comp
    ((measurable_regionGaussianField_noisyRegion μ t _ _).mono
      (noisyRegionSigma_le (A := ℝ) _) le_rfl)).pow_const 2

theorem gaussianInwardConeFactor_mem_Icc {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z) (v : TreeVertex d) :
    gaussianInwardConeFactor μ t theta z v ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := responseAttenuation_pos hθ
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z)
  have hl := responseAttenuation_le_one hθ
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z)
  exact ⟨sq_nonneg _, by unfold gaussianInwardConeFactor; nlinarith⟩

theorem gaussianInwardConeFactor_rootPathVertex {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (v : TreeVertex d) {i : ℕ} (hi : i < v.1.length) (z) :
    gaussianInwardConeFactor μ t theta z (rootPathVertex v (i + 1)) =
      responseAttenuation theta (inwardGaussianField μ t v i z) ^ 2 := by
  change responseAttenuation theta (regionGaussianField μ t
    (cone (ConnectedHull.takeVertex v (i + 1)))ᶜ
    (parentVertex (ConnectedHull.takeVertex v (i + 1))) z) ^ 2 = _
  rw [parent_takeVertex_succ v hi]
  rfl

theorem rootPathProduct_gaussianInwardConeFactor {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (v : TreeVertex d) (z) :
    rootPathProduct (gaussianInwardConeFactor μ t theta z) v =
      ∏ i ∈ Finset.range v.1.length,
        responseAttenuation theta (inwardGaussianField μ t v i z) ^ 2 := by
  apply Finset.prod_congr rfl
  intro i hi
  exact gaussianInwardConeFactor_rootPathVertex μ t theta v (Finset.mem_range.mp hi) z

theorem cutContinuationProduct_gaussianInwardConeFactor {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (z) :
    cutContinuationProduct (gaussianInwardConeFactor μ t theta z) p w =
      ∏ j ∈ Finset.range L, responseAttenuation theta
        (inwardGaussianField μ t (appendCutContinuation p w).1 (k + 1 + j) z) ^ 2 := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [← Nat.add_assoc]
  apply gaussianInwardConeFactor_rootPathVertex
  rw [(appendCutContinuation p w).2]
  exact Nat.add_lt_add_left (Finset.mem_range.mp hj) _

end Problem367

end

end OAI
