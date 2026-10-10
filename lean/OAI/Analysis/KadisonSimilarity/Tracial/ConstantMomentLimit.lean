import OAI.Analysis.KadisonSimilarity.Tracial.DenseMomentExtension
import OAI.Analysis.KadisonSimilarity.Tracial.QuotientMomentLimit

namespace OAI

/-! Trace-density promotes countable quotient moments to every constant coefficient. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower BoundedHochschild Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

def ConstantIntegerMoments (u : ℕ → unitary B) : Prop :=
  ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
    (∀ b ∈ l, b.1 ≠ 0) → quotientTrace τ h1 ω tr
      (integerEval (fun x => constant τ h1 ω tr x - τ x • 1)
        (quotientUnitary τ h1 ω tr u) a l) = 0

theorem constantIntegerMoments_of_dense (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : ℕ → unitary B)
    (hu : AllQuotientMoments τ h1 ω tr (fun i => BoundedContinuousFunction.const ℕ (d i)) u) :
    ConstantIntegerMoments τ h1 ω tr u := by
  let T := quotientTrace τ h1 ω tr
  let φ := constant τ h1 ω tr
  let W := quotientUnitary τ h1 ω tr u
  have hm (a : Option ℕ) (l : List (IntAtom ℕ)) (hl : admissibleIntTail l)
      (hk : ∀ b ∈ l, b.1 ≠ 0) :
      T (integerEval (fun n => φ (d n) - T (φ (d n)) • 1) W a l) = 0 :=
    integer_moments_of_bounded T (fun n => φ (d n) - T (φ (d n)) • 1) W hu a l hl hk
  intro a l hl hk
  have hz := all_integer_moments_of_trace_dense τ T (quotientTrace_one τ h1 ω tr)
    (quotientTrace_tracial τ h1 ω tr) φ (quotientTrace_constant τ h1 ω tr)
    d hd hdense W hm (fun x : B => x) a l hl hk
  simpa only [φ, T, quotientTrace_constant] using hz

end KadisonSimilarity

end

end OAI
