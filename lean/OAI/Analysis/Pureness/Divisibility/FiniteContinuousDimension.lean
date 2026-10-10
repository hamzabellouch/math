import OAI.Analysis.Pureness.Divisibility.ContinuousSupportComparison
import OAI.Analysis.Pureness.Traces.ContinuousDimensionIntegral
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralOrder

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Set MeasureTheory
open scoped ComplexOrder NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteContinuousDimension (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f : C(X, ℝ≥0)) : ℝ≥0∞ :=
  d (finitePositiveClass n (Positive.map φ (continuousNNRealPositive f)))

lemma finiteContinuousDimension_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) : Monotone (finiteContinuousDimension d n φ) := by
  intro f g hfg
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  apply (cuntzSubequiv_iff_shared _ _).mpr
  exact (CuntzBelow.of_le _ _ (continuousNNRealPositive_mono hfg)).map φ

lemma positiveMap_continuousNNReal_add (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n)
    (f g : C(X, ℝ≥0)) :
    Positive.map φ (continuousNNRealPositive (f+g)) =
      Positive.add (Positive.map φ (continuousNNRealPositive f)) (Positive.map φ (continuousNNRealPositive g)) := by
  rw [continuousNNRealPositive_add]
  apply Subtype.ext
  exact map_add φ _ _

lemma finiteContinuousDimension_add_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0)) :
    finiteContinuousDimension d n φ (f+g) ≤ finiteContinuousDimension d n φ f+finiteContinuousDimension d n φ g := by
  unfold finiteContinuousDimension
  rw [positiveMap_continuousNNReal_add,← map_add]
  exact hd (finitePositiveClass_sum_le n _ _)

lemma finiteContinuousDimension_add_orthogonal
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0)) (h : f*g = 0) :
    finiteContinuousDimension d n φ (f+g) = finiteContinuousDimension d n φ f+finiteContinuousDimension d n φ g := by
  unfold finiteContinuousDimension
  rw [positiveMap_continuousNNReal_add,finitePositiveClass_orthogonal_add,map_add]
  change φ (continuousNNRealPositive f).1*φ (continuousNNRealPositive g).1 = 0
  rw [← map_mul,continuousNNRealPositive_mul_zero f g h,map_zero]

lemma finiteContinuousDimension_support_mono
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0))
    (h : ∀ x, 0 < f x → 0 < g x) :
    finiteContinuousDimension d n φ f ≤ finiteContinuousDimension d n φ g := by
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  apply (cuntzSubequiv_iff_shared _ _).mpr
  exact (continuousNNRealPositive_cuntzBelow_of_support f g h).map φ

lemma finiteContinuousDimension_cuts
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f : C(X, ℝ≥0)) :
    finiteContinuousDimension d n φ f = ⨆ (ε : ℝ≥0) (_ : 0 < ε), finiteContinuousDimension d n φ (continuousNNRealCut ε f) := by
  have hreg := congrArg (fun e : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞ =>
    e (finitePositiveClass n (Positive.map φ (continuousNNRealPositive f))))
    (regularizedFiniteDimension_eq_of_lowerSemicontinuous d hd hlsc)
  rw [regularizedFiniteDimension_eval] at hreg
  unfold finiteContinuousDimension
  rw [← hreg]
  simp only [finiteRegularizedValue,continuousNNRealPositive_cut,Positive.map_cut]
end CuntzPureness

end

end OAI
