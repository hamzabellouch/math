import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialHaarPerturbation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! Strong continuity of a unitary action gives every weak Haar integral
used in symmetrization. No continuity in operator norm is required. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
/-- Moving the left unitary to the second inner-product slot makes matrix
coefficients of its conjugation action continuous in the strong topology. -/
theorem continuous_unitaryConjugate_coefficient
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) (x y : H) :
    Continuous (fun g => inner ℂ (unitaryConjugate U T g x) y) := by
  have he : (fun g => inner ℂ (unitaryConjugate U T g x) y) =
      fun g => inner ℂ (T (U g⁻¹ x)) (U g⁻¹ y) := by
    funext g
    change inner ℂ (U g (T (U g⁻¹ x))) y = _
    rw [← adjoint_inner_right, hstar]
  rw [he]
  exact (T.continuous.comp ((hcont x).comp continuous_inv)).inner
    ((hcont y).comp continuous_inv)

/-- On a compact group these continuous scalar coefficients are integrable
against Haar probability measure. -/
theorem weaklyIntegrable_unitaryConjugate (μ : Measure Γ) [IsFiniteMeasure μ]
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) :
    WeaklyIntegrable μ (unitaryConjugate U T) := by
  intro x y
  exact (continuous_unitaryConjugate_coefficient U hstar hcont T x y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end KadisonSimilarity

end

end OAI
