import OAI.Analysis.KadisonSimilarity.Representation.FactorAssembly
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorTrace
import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualRestriction

namespace OAI

/-! Construct the finite-factor model from a concrete subfactor and its
matrix presentation. The source trace and both GNS normality proofs are
derived from the ambient normal trace. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N P : VonNeumannAlgebra H} (hNP : N ≤ P)
  (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)
  (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))

include h1 in
theorem includedPositiveTrace_one : includedPositiveTrace hNP τ 1 = 1 := h1

include htr in
theorem includedPositiveTrace_tracial (a b : N.toStarSubalgebra) :
    includedPositiveTrace hNP τ (a * b) = includedPositiveTrace hNP τ (b * a) := by
  simpa only [includedPositiveTrace_apply, map_mul] using
    htr (StarSubalgebra.inclusion hNP a) (StarSubalgebra.inclusion hNP b)

theorem includedPositiveTrace_faithful
    (hf : ∀ a, τ (star a * a) = 0 → a = 0)
    (a : N.toStarSubalgebra) (ha : includedPositiveTrace hNP τ (star a * a) = 0) : a = 0 := by
  apply Subtype.ext
  have hz : τ (star (StarSubalgebra.inclusion hNP a) *
      StarSubalgebra.inclusion hNP a) = 0 := by
    simpa only [includedPositiveTrace_apply, map_mul, map_star] using ha
  exact congrArg (fun b : P.toStarSubalgebra => (b : H →L[ℂ] H)) (hf _ hz)

variable (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  (hnormal : TraceInPredual (concretePredualEquiv P) τ)
  (size : ℕ → ℕ) [hsize : ∀ j, Nonempty (Fin (size j))]
  (matrices : NestedTracialMatrices (A := fun j => Fin (size j))
    (includedPositiveTrace hNP τ).toLinearMap (gnsTracialVector (includedPositiveTrace hNP τ)))
  (size_tendsto : Filter.Tendsto (fun j => (Fintype.card (Fin (size j)) : ℝ))
    Filter.atTop Filter.atTop)
  (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
  (free_position : FiniteFactorFreeCornerInputs (includedPositiveTrace hNP τ) τ
    (includedPositiveTrace_one hNP τ h1) h1 ω
    (includedPositiveTrace_tracial hNP τ htr) htr
    (StarSubalgebra.inclusion hNP) (fun _ => rfl) hω)

/-- The finite-factor presentation has no separate trace-normality or
source-trace existence premise. -/
def concreteFiniteFactorModel : FiniteFactorModel P where
  R := N.toStarSubalgebra
  traceR := includedPositiveTrace hNP τ
  traceP := τ
  oneR := includedPositiveTrace_one hNP τ h1
  oneP := h1
  tracialR := includedPositiveTrace_tracial hNP τ htr
  tracialP := htr
  faithfulR := includedPositiveTrace_faithful hNP τ hf
  faithfulP := hf
  normalR := includedPositiveTrace_hasNormalGNS hNP τ hnormal htr
  normalP := hasNormalGNS_of_predual (concretePredualEquiv P) τ hnormal htr
  inclusion := StarSubalgebra.inclusion hNP
  trace_inclusion := fun _ => rfl
  size := size
  stageNonempty := hsize
  matrices := matrices
  size_tendsto := size_tendsto
  omega := ω
  omega_cofinite := hω
  localInputs := free_position

include hNP τ h1 htr hf hnormal size matrices size_tendsto ω hω free_position in
theorem concrete_finite_factor_estimate [TopologicalSpace.SeparableSpace H] :
    CommutatorEstimate P (3 * cornerConstant + 2) :=
  (concreteFiniteFactorModel hNP τ h1 htr hf hnormal size matrices size_tendsto
    ω hω free_position).estimate

end KadisonSimilarity

end

end OAI
