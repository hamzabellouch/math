import Mathlib
import OAI.Geometry.SmoothYau.Geometry.TestElliptic

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def weightedPair (a : SmoothScalar E) (f g : EllipticTest K) : ℝ :=
  testPair K (testMultiply K a f) g
lemma weightedPair_symm (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f g = weightedPair K a g f := by
  unfold weightedPair
  rw [testMultiply_symmetric, testPair_comm]
lemma weightedPair_add_coeff (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (a+b) f g = weightedPair K a f g + weightedPair K b f g := by
  simp only [weightedPair, testMultiply_add, testPair_add_left]
lemma weightedPair_smul_coeff (c : ℝ) (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (c • a) f g = c * weightedPair K a f g := by
  simp only [weightedPair, testMultiply_smul, testPair_smul_left]
lemma weightedPair_sum_coeff {ι : Type*} (s : Finset ι) (a : ι → SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (∑ i ∈ s, a i) f g = ∑ i ∈ s, weightedPair K (a i) f g := by
  simp only [weightedPair, testMultiply_sum, testPair_sum_left]
lemma weightedPair_add_left (a : SmoothScalar E) (f g h : EllipticTest K) :
    weightedPair K a (f+g) h = weightedPair K a f h + weightedPair K a g h := by
  simp only [weightedPair, map_add, testPair_add_left]
lemma weightedPair_add_right (a : SmoothScalar E) (f g h : EllipticTest K) :
    weightedPair K a f (g+h) = weightedPair K a f g + weightedPair K a f h := by
  simp only [weightedPair, testPair_add_right]
lemma weightedPair_sum_left {ι : Type*} (s : Finset ι) (a : SmoothScalar E)
    (f : ι → EllipticTest K) (g : EllipticTest K) :
    weightedPair K a (∑ i ∈ s, f i) g = ∑ i ∈ s, weightedPair K a (f i) g := by
  simp only [weightedPair, map_sum, testPair_sum_left]
lemma weightedPair_sum_right {ι : Type*} (s : Finset ι) (a : SmoothScalar E)
    (f : EllipticTest K) (g : ι → EllipticTest K) :
    weightedPair K a f (∑ i ∈ s, g i) = ∑ i ∈ s, weightedPair K a f (g i) := by
  simp only [weightedPair, testPair_sum_right]
lemma weightedPair_mul (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f (testMultiply K b g) = weightedPair K (a*b) f g := by
  unfold weightedPair
  rw [← testMultiply_symmetric, ← testMultiply_mul, mul_comm b a]
lemma weightedPair_derivative (a : SmoothScalar E) (v : E) (f g : EllipticTest K) :
    weightedPair K a (testDerivative K v f) g + weightedPair K a f (testDerivative K v g) =
      -weightedPair K (SmoothScalar.directional v a) f g :=
  testPair_weighted_derivative K a v f g
lemma weightedPair_self_derivative (a : SmoothScalar E) (v : E) (f : EllipticTest K) :
    2 * weightedPair K a f (testDerivative K v f) =
      -weightedPair K (SmoothScalar.directional v a) f f :=
  testPair_weighted_self_derivative K a v f
end YauCounterexamples

end

end OAI
