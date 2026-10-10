import OAI.Analysis.Pureness.Quasitrace.QuasitraceWeightedAddition
import OAI.Analysis.Pureness.Operators.WeightedScalarOptimization

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralPositiveQuasitrace_sqrt_add
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤)
    (n : ℕ) (M N : Positive (FinMatrix A n)) :
    Real.sqrt (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n (Positive.add M N)) ≤
      Real.sqrt (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n M)+
      Real.sqrt (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n N) := by
  let T := finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
  have h := weighted_scalar_sqrt_bound (T M) (T N) (T (Positive.add M N)) (T.nonneg M) (T.nonneg N)
    (fun r hr => finiteSpectralPositiveQuasitrace_add_weighted d hd hlsc hfinite n M N r hr)
  exact (Real.sqrt_le_iff.mpr ⟨by positivity,h⟩)
end CuntzPureness

end

end OAI
