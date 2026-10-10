import OAI.Analysis.KadisonSimilarity.FreeProduct.FiniteFactorFreeness
import OAI.Analysis.KadisonSimilarity.ConditionalMain

namespace OAI

/-! The factor alternatives are proved, including zero Hilbert fibers.
Only the central decomposition itself remains a structural input here. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H)

theorem publishedFactorCases_of_scalar_center
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    PublishedFactorCasesInput P := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · let := hs
    let σ : Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) := {
      toFun := fun _ => 0
      map_zero' := rfl
      map_add' := fun _ _ => by simp
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => by simp
      commutes' := fun _ => Subsingleton.elim _ _
      map_star' := fun _ => by simp }
    exact Or.inr (Or.inr ⟨{
      size := 1
      size_ne_zero := by decide
      inclusion := σ
      mem := fun _ => P.zero_mem
      surjective := fun T _ => ⟨0, Subsingleton.elim _ _⟩ }⟩)
  · let := hn
    exact publishedFactorCases hfactor

/-- The manuscript's factor-representation bound, with every local input proved. -/
theorem factorCommutatorEstimate
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    CommutatorEstimate P factorConstant :=
  factor_estimate_of_published_cases P (publishedFactorCases_of_scalar_center P hfactor)
    dicksonTwoBound_proved

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]
  [∀ a, TopologicalSpace.SeparableSpace (K a)]

/-- A central decomposition into actual factors suffices; no factor model
or free-position hypothesis is required from the decomposition theorem. -/
def publishedSeparableModel_of_central_factors
    (D : CentralDecompositionData μ K P)
    (hfactor : ∀ᵐ a ∂μ, ∀ x : (D.algebra a).toStarSubalgebra,
      (∀ y, x * y = y * x) →
        ∃ z : ℂ, x = algebraMap ℂ (D.algebra a).toStarSubalgebra z) :
    PublishedSeparableModel P where
  Ω := Ω
  measure := μ
  K := K
  decomposition := D
  cases := hfactor.mono fun a ha => publishedFactorCases_of_scalar_center (D.algebra a) ha

end KadisonSimilarity

end

end OAI
