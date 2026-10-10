import OAI.Analysis.CircleDomains.Topology.PathImageCount
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! The plane-to-line specialization of Esmayli–Hajłasz, *The Coarea
Inequality*, Ann. Fenn. Math. 46 (2021), 965–991, Theorem 1.1,
DOI 10.5186/aasfm.2021.4654. The authors' manuscript is
https://arxiv.org/pdf/2006.00419 (Theorem 1.1, p. 1; proof, §7).

Only s=t=1, X=ℂ and Y=ℝ is retained. The Hausdorff normalization
constant is one in these dimensions. The source's measurability clause
requires finite H¹ measure and a measurable set in a boundedly compact
space; all these hypotheses are retained. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

 def PlanarLipschitzFiberCoarea : Prop :=
  ∀ (A : Set ℂ), MeasurableSet A → (μH[1] : Measure ℂ) A < ∞ →
    ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f →
      AEMeasurable (fun y => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {y})) volume ∧
      (∫⁻ y, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {y})) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure ℂ) A

 theorem cardinalitySum_le_hausdorffZero (A : Set ℂ) :
    (∑' z : ℂ, if z ∈ A then (1 : ℝ≥0∞) else 0) ≤ (μH[0] : Measure ℂ) A := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let E := F.filter (fun z => z ∈ A)
  calc
    (∑ z ∈ F, if z ∈ A then (1 : ℝ≥0∞) else 0) =
        ∑ z ∈ E, (μH[0] : Measure ℂ) {z} := by
      simp only [E, Finset.sum_filter, Measure.hausdorffMeasure_zero_singleton]
    _ = (μH[0] : Measure ℂ) E := sum_measure_singleton
    _ ≤ (μH[0] : Measure ℂ) A := measure_mono (fun z hz => (Finset.mem_filter.mp hz).2)

 theorem pathImageCount_le_hausdorffZero (A : Set ℂ) (γ : C(PathTime, ℂ)) :
    pathImageCount A γ ≤ (μH[0] : Measure ℂ) (range γ ∩ A) :=
by
  simpa [pathImageCount, Set.mem_inter_iff] using cardinalitySum_le_hausdorffZero (range γ ∩ A)

 theorem integrated_pathImageCount_le_length (hcoarea : PlanarLipschitzFiberCoarea)
    (γ : C(PathTime, ℂ)) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : (μH[1] : Measure ℂ) (range γ ∩ A) < ∞)
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, pathImageCount (A ∩ f ⁻¹' {y}) γ) ≤
      (L : ℝ≥0∞) * (μH[1] : Measure ℂ) (range γ ∩ A) := by
  apply le_trans (lintegral_mono (fun y => ?_))
    (hcoarea (range γ ∩ A) ((isCompact_range γ.continuous).isClosed.measurableSet.inter hA)
      hfin L f hf).2
  simpa only [inter_assoc] using pathImageCount_le_hausdorffZero (A ∩ f ⁻¹' {y}) γ

end CircleDomainRigidity

end

end OAI
