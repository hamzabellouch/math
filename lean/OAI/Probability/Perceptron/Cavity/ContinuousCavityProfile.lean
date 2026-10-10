import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkPairLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cappedA_monotone (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ} (hB : B < 1) :
    Monotone (cappedA μ B) :=
  monotone_of_hasDerivAt_nonneg (cappedA_hasDerivAt μ hB) (fun _ => sq_nonneg _)

def continuousCavityProfile (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) : BulkPairRange K :=
  (⟨r.val, (by linarith [r.prop.1]), r.prop.2⟩,
    ⟨min d (max 0 (cappedA μ B r)), by
      constructor
      · have hm := le_min hd0 (le_max_left 0 (cappedA μ B r))
        linarith
      · exact (min_le_left _ _).trans hdK⟩)

def cavityTrueDiagonal {K d : ℝ} (hd0 : 0 ≤ d) (hdK : d ≤ K) : BulkPairRange K :=
  (⟨1,by norm_num⟩,⟨d,by constructor <;> linarith⟩)

lemma continuousCavityProfile_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K) :
    Continuous (continuousCavityProfile μ B hd0 hdK) := by
  have hc : Continuous (fun r : Time => cappedA μ B r.val) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  exact (continuous_subtype_val.subtype_mk _).prodMk
    ((continuous_const.min (continuous_const.max hc)).subtype_mk _)

lemma continuousCavityProfile_mono (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K) :
    Monotone (fun r => (continuousCavityProfile μ B hd0 hdK r).2.val) := by
  exact monotone_const.min (monotone_const.max
    ((cappedA_monotone μ hB).comp (Subtype.mono_coe _)))

lemma continuousCavityProfile_nonneg (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) :
    0 ≤ (continuousCavityProfile μ B hd0 hdK r).1.val ∧
    0 ≤ (continuousCavityProfile μ B hd0 hdK r).2.val :=
  ⟨r.prop.1,le_min hd0 (le_max_left _ _)⟩

lemma continuousCavityProfile_le_diagonal (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) :
    (continuousCavityProfile μ B hd0 hdK r).1.val ≤ (cavityTrueDiagonal hd0 hdK).1.val ∧
    (continuousCavityProfile μ B hd0 hdK r).2.val ≤ (cavityTrueDiagonal hd0 hdK).2.val :=
  ⟨r.prop.2,min_le_left _ _⟩

lemma continuousCavityProfile_eq (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hd0 : 0 ≤ d) (hdK : d ≤ K)
    (hμ : ∀ᵐ r : Time ∂μ, r.val ≤ B) {r : Time} {a : ℝ}
    (hr : r.val ≤ B) (ha0 : 0 ≤ a) (had : a ≤ d)
    (ha : a = ∫ t in 0..r.val, (realTail μ t)⁻¹^2) :
    (continuousCavityProfile μ B hd0 hdK r).2.val = a := by
  change min d (max 0 (cappedA μ B r.val)) = a
  rw [cappedA_eq_integral μ hμ r.prop.1 hr,←ha,max_eq_right ha0,min_eq_right had]

end SphericalPerceptronFreeEnergy

end

end OAI
