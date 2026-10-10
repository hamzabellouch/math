import OAI.Analysis.Pureness.Projections.QuotientProjectionNormality
import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltraproductAWEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology ComplexOrder
variable {ι : Type*} [Nonempty ι] {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)]
variable (T : ∀ i, PositiveQuasitrace (D i)) (U : Ultrafilter ι)
variable (hunit : ∀ i, T i ⟨1, zero_le_one⟩ = 1)
variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x+(T i).metricSize y)
variable (hsqrt : ∀ i (a b : Positive (D i)), Real.sqrt (T i (Positive.add a b)) ≤
      Real.sqrt (T i a)+Real.sqrt (T i b))

theorem ultralimitAWQuasitrace_normal
    (S : Set (UltralimitAWCompletion T U hunit hadd)) (hne : S.Nonempty)
    (hproj : ∀ p ∈ S, IsStarProjection p) (hdir : DirectedOn (· ≤ ·) S) :
    ∃ p : UltralimitAWCompletion T U hunit hadd, IsStarProjection p ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ q, IsStarProjection q → (∀ a ∈ S, a ≤ q) → p ≤ q) ∧
      (ultralimitAWQuasitrace T U hunit hadd hsqrt p).re =
        sSup ((fun q => (ultralimitAWQuasitrace T U hunit hadd hsqrt q).re) '' S) := by
  simpa only [ultralimitAWQuasitrace, PositiveQuasitrace.quotientComplexQuasitrace_eq] using
    (ultralimitPositiveQuasitrace T U hunit).exists_quotient_directed_projection_sup
      (ultralimitPositiveQuasitrace_metricSize_add T U hunit hadd)
      (ultralimitPositiveQuasitrace_sqrt_add T U hunit hsqrt) S hne hproj hdir
end CuntzPureness

end

end OAI
