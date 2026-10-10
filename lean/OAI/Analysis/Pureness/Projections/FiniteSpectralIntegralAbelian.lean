import OAI.Analysis.Pureness.Divisibility.FiniteContinuousDimension

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Set MeasureTheory
open scoped ComplexOrder NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [T2Space X] in
lemma finiteSpectralIntegral_image_eq (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f : C(X, ℝ≥0)) :
    finiteSpectralIntegral d n (Positive.map φ (continuousNNRealPositive f)) =
      continuousDimensionIntegral (finiteContinuousDimension d n φ) f := by
  simp only [finiteSpectralIntegral,finiteDimensionDistribution,continuousDimensionIntegral,
    finiteContinuousDimension,continuousNNRealPositive_cut,Positive.map_cut]

theorem finiteSpectralIntegral_image_add
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0)) :
    finiteSpectralIntegral d n (Positive.add (Positive.map φ (continuousNNRealPositive f))
      (Positive.map φ (continuousNNRealPositive g))) =
      finiteSpectralIntegral d n (Positive.map φ (continuousNNRealPositive f)) +
      finiteSpectralIntegral d n (Positive.map φ (continuousNNRealPositive g)) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  rw [← positiveMap_continuousNNReal_add,finiteSpectralIntegral_image_eq,
    finiteSpectralIntegral_image_eq,finiteSpectralIntegral_image_eq]
  exact continuousDimensionIntegral_add (finiteContinuousDimension d n φ) (hfinite _)
    (finiteContinuousDimension_monotone d hd n φ) (finiteContinuousDimension_add_le d hd n φ)
    (finiteContinuousDimension_add_orthogonal d n φ) (finiteContinuousDimension_support_mono d hd n φ)
    (finiteContinuousDimension_cuts d hd hlsc n φ) f g
end CuntzPureness

end

end OAI
