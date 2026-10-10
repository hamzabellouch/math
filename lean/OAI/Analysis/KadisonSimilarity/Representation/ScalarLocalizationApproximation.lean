import OAI.Analysis.KadisonSimilarity.Representation.ContinuousL2Multiplication
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Uniformly bounded continuous functions approximate the measurable
scalar localizations needed in the central spectral model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] [μ.Regular]

theorem exists_continuous_indicator_eLpNorm_approx (s : Set X) (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C(X, ℂ), (∀ x, ‖f x‖ ≤ 1) ∧
      eLpNorm (fun x => f x - s.indicator (fun _ => (1 : ℂ)) x) 2 μ ≤ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_Lp_half ℂ μ 2 hε
  obtain ⟨η, hηpos, hη⟩ := exists_eLpNorm_indicator_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (1 : ℂ) hδpos.ne'
  have hηpos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hηpos
  obtain ⟨F, hFs, _, hFc, hμF⟩ :=
    hs.exists_isCompact_isClosed_sdiff_lt (measure_ne_top μ s) hηpos'.ne'
  have hI : eLpNorm ((F.indicator fun _ => (1 : ℂ)) -
      s.indicator (fun _ => (1 : ℂ))) 2 μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hFs]
    exact hη _ hμF.le (hs.diff hFc.measurableSet).nullMeasurableSet
  obtain ⟨g, hgc, hgd, hgb, _, _⟩ := exists_continuous_eLpNorm_sub_le_of_closed
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hFc isOpen_univ (subset_univ F)
    (measure_ne_top μ F) (1 : ℂ) hδpos.ne'
  refine ⟨⟨g, hgc⟩, ?_, ?_⟩
  · intro x
    change ‖g x‖ ≤ 1
    simpa only [norm_one] using hgb x
  · convert! (hδ _ _ hgd hI).le using 2
    ext x
    simp

end KadisonSimilarity

end

end OAI
