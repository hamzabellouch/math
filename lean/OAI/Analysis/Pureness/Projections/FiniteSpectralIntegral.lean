import OAI.Analysis.Pureness.States.FiniteRegularizationProjections
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteDimensionDistribution (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (M : Positive (FinMatrix A n)) (t : ℝ) : ℝ≥0∞ :=
  d (finitePositiveClass n (Positive.cut t.toNNReal M))

lemma finiteDimensionDistribution_antitone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Antitone (finiteDimensionDistribution d n M) := by
  intro s t hst
  exact finiteCutValue_antitone d hd n M (Real.toNNReal_mono hst)

lemma finiteDimensionDistribution_measurable
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Measurable (finiteDimensionDistribution d n M) :=
  (finiteDimensionDistribution_antitone d hd n M).measurable

def finiteSpectralIntegral (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (M : Positive (FinMatrix A n)) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), finiteDimensionDistribution d n M t

lemma finiteSpectralIntegral_zero (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (n : ℕ) :
    finiteSpectralIntegral d n Positive.zero = 0 := by
  have hcut (t : ℝ) : Positive.cut t.toNNReal (Positive.zero : Positive (FinMatrix A n)) = Positive.zero := by
    apply Subtype.ext
    simp [Positive.cut,Positive.zero]
  simp [finiteSpectralIntegral,finiteDimensionDistribution,hcut,finitePositiveClass_zero]

theorem finiteSpectralIntegral_inclusion
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    finiteSpectralIntegral d m (Positive.map (matrixInclusion h) M) = finiteSpectralIntegral d n M := by
  simp only [finiteSpectralIntegral,finiteDimensionDistribution,← Positive.map_cut,finitePositiveClass_inclusion]

theorem finiteSpectralIntegral_block_add
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finiteSpectralIntegral d (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      finiteSpectralIntegral d n M+finiteSpectralIntegral d n N := by
  simp only [finiteSpectralIntegral,finiteDimensionDistribution,finitePositiveClass_cut_add,map_add]
  exact lintegral_add_left (finiteDimensionDistribution_measurable d hd n M) _
end CuntzPureness

end

end OAI
