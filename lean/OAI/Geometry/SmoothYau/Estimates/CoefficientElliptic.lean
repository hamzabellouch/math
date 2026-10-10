import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.WeightedPair

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def coefficientElliptic (a : ι → ι → SmoothScalar E) (q : SmoothScalar E) : SmoothScalar E :=
  ∑ i, ∑ j, SmoothScalar.directional (e i) (a i j * SmoothScalar.directional (e j) q)

lemma testElliptic_multiplier_pair (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (q : SmoothScalar E) (f : EllipticTest K) :
    2 * testPair K (testElliptic K e a f) (testMultiply K q f) =
      weightedPair K (coefficientElliptic e a q) f f -
        2 * ∑ i, ∑ j, weightedPair K (a i j * q)
          (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  have hcross (i j : ι) :
      2 * weightedPair K (a i j * SmoothScalar.directional (e i) q)
        (testDerivative K (e j) f) f =
      -weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f := by
    rw [weightedPair_symm K _ (testDerivative K (e j) f)]
    exact weightedPair_self_derivative K _ (e j) f
  rw [testElliptic_pair]
  unfold testEnergy
  simp only [show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl,
    testProductRule, weightedPair_add_right, weightedPair_mul, Finset.sum_add_distrib,
    mul_neg, Finset.mul_sum]
  have he : weightedPair K (coefficientElliptic e a q) f f =
      ∑ i, ∑ j, weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f := by
    simp only [coefficientElliptic, weightedPair_sum_coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  rw [he]
  have hc : 2 * (∑ i, ∑ j, weightedPair K (a i j * SmoothScalar.directional (e i) q)
      (testDerivative K (e j) f) f) =
      -(∑ i, ∑ j, weightedPair K (SmoothScalar.directional (e j)
        (a i j * SmoothScalar.directional (e i) q)) f f) := by
    simp only [Finset.mul_sum, hcross, Finset.sum_neg_distrib]
  simp only [← Finset.mul_sum]
  linarith

lemma testElliptic_transport_pair (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (f : EllipticTest K) :
    2 * testPair K (testElliptic K e a f) (testTransport K e X f) =
      -2 * (∑ i, ∑ j, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) +
      ∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  let T (i j k : ι) := weightedPair K (a i j * X k) (testDerivative K (e j) f)
    (testDerivative K (e k) (testDerivative K (e i) f))
  have hT (i j k : ι) : T i j k + T j i k =
      -weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
    dsimp only [T]
    rw [ha j i, weightedPair_symm K _ (testDerivative K (e i) f)]
    have hh := weightedPair_derivative K (a i j * X k) (e k)
      (testDerivative K (e j) f) (testDerivative K (e i) f)
    linarith
  have hswap : (∑ i, ∑ j, ∑ k, T j i k) = ∑ i, ∑ j, ∑ k, T i j k :=
    Finset.sum_comm
  have hcancel : 2 * (∑ i, ∑ j, ∑ k, T i j k) =
      -(∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) := by
    calc
      _ = (∑ i, ∑ j, ∑ k, (T i j k + T j i k)) := by
        simp only [Finset.sum_add_distrib, hswap]; ring
      _ = _ := by simp only [hT, Finset.sum_neg_distrib]
  rw [testElliptic_pair]
  unfold testEnergy testTransport
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, weightedPair_sum_right,
    testProductRule, weightedPair_add_right,
    show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl,
    weightedPair_mul,
    Finset.sum_add_distrib]
  have hreorder (i j k : ι) : weightedPair K (a i j * X k)
      (testDerivative K (e j) f) (testDerivative K (e i) (testDerivative K (e k) f)) =
      T i j k := by
    rw [testDerivative_comm K (e i) (e k)]
  simp only [hreorder]
  linarith
end YauCounterexamples

end

end OAI
