import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.TestDerivativeComm

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]
variable (e : ι → E)

def testElliptic (a : ι → ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  ∑ i, ∑ j, (testDerivative K (e i)).comp ((testMultiply K (a i j)).comp (testDerivative K (e j)))
def testTransport (X : ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  ∑ i, (testMultiply K (X i)).comp (testDerivative K (e i))
def coefficientDivergence (X : ι → SmoothScalar E) : SmoothScalar E :=
  ∑ i, SmoothScalar.directional (e i) (X i)
def testSkewTransport (X : ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (2 : ℝ) • testTransport K e X + testMultiply K (coefficientDivergence e X)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def testEnergy (a : ι → ι → SmoothScalar E) (f g : EllipticTest K) : ℝ :=
  ∑ i, ∑ j, testPair K (testMultiply K (a i j) (testDerivative K (e j) f)) (testDerivative K (e i) g)

lemma testElliptic_pair (a : ι → ι → SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testElliptic K e a f) g = -testEnergy K e a f g := by
  simp only [testElliptic, LinearMap.sum_apply, LinearMap.comp_apply, testPair_sum_left,
    testDerivative_skew, Finset.sum_neg_distrib, testEnergy]

lemma testEnergy_symmetric (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (f g : EllipticTest K) :
    testEnergy K e a f g = testEnergy K e a g f := by
  unfold testEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i, testMultiply_symmetric, testPair_comm]

lemma testElliptic_symmetric (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (f g : EllipticTest K) :
    testPair K (testElliptic K e a f) g = testPair K f (testElliptic K e a g) := by
  rw [testPair_comm K f, testElliptic_pair, testElliptic_pair, testEnergy_symmetric K e a ha]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma testMultiply_sum {η : Type*} (s : Finset η) (a : η → SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (∑ i ∈ s, a i) f = ∑ i ∈ s, testMultiply K (a i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext x
    simp [testMultiply_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, testMultiply_add, ih]

lemma testTransport_pair (X : ι → SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testTransport K e X f) g + testPair K f (testTransport K e X g) =
      -testPair K (testMultiply K (coefficientDivergence e X) f) g := by
  simp only [testTransport, LinearMap.sum_apply, LinearMap.comp_apply,
    testPair_sum_left, testPair_sum_right, coefficientDivergence, testMultiply_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← testMultiply_symmetric]
  exact testPair_weighted_derivative K (X i) (e i) f g

lemma testSkewTransport_skew (X : ι → SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testSkewTransport K e X f) g = -testPair K f (testSkewTransport K e X g) := by
  have h := testTransport_pair K e X f g
  simp only [testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_add_left, testPair_add_right, testPair_smul_left, testPair_smul_right]
  rw [← testMultiply_symmetric]
  linarith
end YauCounterexamples

end

end OAI
