import OAI.Probability.SpanningForest.SampledPathConcatenation
import OAI.Probability.SpanningForest.DenseGaussianModification

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Problem336.GlobalWiener

abbrev Path := C(ℝ≥0, ℝ)

local instance : MeasurableSpace C(ℝ, ℝ) := borel _
local instance : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace Path := borel _
local instance : BorelSpace Path := ⟨rfl⟩

def nonnegativeEmbedding : C(ℝ≥0, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

def samplePath (ω : ℕ → ℝ) : Path :=
  (SampledPathConcatenation.fullPath DyadicTimes.enumeration ω).comp nonnegativeEmbedding

lemma measurable_samplePath : Measurable samplePath :=
  (ContinuousMap.continuous_precomp nonnegativeEmbedding).measurable.comp
    (SampledPathConcatenation.measurable_fullPath DyadicTimes.enumeration)

theorem isBrownian_samplePath {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ
      (CountableBrownian.family DyadicTimes.enumeration)) :
    IsBrownianReal (fun t ω => samplePath ω t) μ := by
  apply DenseBrownian.isBrownian_of_dense_gaussian_modification
    (τ := DyadicTimes.enumeration) (Y := fun i ω => ω i)
    DenseBrownian.dense_dyadicTimes
  · intro t
    exact (continuous_eval_const t).measurable.comp measurable_samplePath
  · exact ae_of_all _ (fun ω => (samplePath ω).continuous)
  · exact CountableBrownian.isGaussianProcess hμ
  · exact CountableBrownian.integral_eval hμ
  · exact CountableBrownian.covariance_eval hμ
  · intro t ht
    obtain ⟨n, k, rfl⟩ := ht
    refine ⟨Nat.pair n k, ?_, ?_⟩
    · simp [DyadicTimes.grid]
    · filter_upwards [SampledPathConcatenation.ae_fullPath_coordinates hμ Nat.pair
        (by intro n k; simp [DyadicTimes.grid])] with ω hω
      change SampledPathConcatenation.fullPath DyadicTimes.enumeration ω
        (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) = ω (Nat.pair n k)
      simpa using hω n k

theorem exists_wiener :
    ∃ ρ : Measure Path, IsProbabilityMeasure ρ ∧
      IsBrownianReal (fun t (w : Path) => w t) ρ := by
  obtain ⟨μ, hprob, hμ⟩ :=
    CountableBrownian.exists_countable_brownian_law DyadicTimes.enumeration
  let : IsProbabilityMeasure μ := hprob
  let ρ : Measure Path := μ.map samplePath
  have hρ : IsProbabilityMeasure ρ :=
    inferInstance
  have hB := isBrownian_samplePath hμ
  refine ⟨ρ, hρ, ?_⟩
  constructor
  · constructor
    intro I
    have hm : Measurable (fun w : Path => I.restrict (fun t => w t)) :=
      Measurable.of_eval (fun i => (continuous_eval_const i.val).measurable)
    refine ⟨hm.aemeasurable, ?_⟩
    change (μ.map samplePath).map (fun w : Path => I.restrict (fun t => w t)) = _
    rw [Measure.map_map hm measurable_samplePath]
    exact (hB.toIsPreBrownianReal.hasLaw I).map_eq
  · exact ae_of_all _ (fun w => w.continuous)

def wienerMeasure : Measure Path := Classical.choose exists_wiener

instance wienerMeasure_isProbabilityMeasure : IsProbabilityMeasure wienerMeasure :=
  (Classical.choose_spec exists_wiener).1

theorem isBrownian_wienerMeasure :
    IsBrownianReal (fun t (w : Path) => w t) wienerMeasure :=
  (Classical.choose_spec exists_wiener).2

end Problem336.GlobalWiener

end

end OAI
