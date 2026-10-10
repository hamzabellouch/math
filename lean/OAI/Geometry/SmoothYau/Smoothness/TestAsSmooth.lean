import Mathlib
import OAI.Geometry.SmoothYau.Estimates.TestPairSubSquareBound

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def testAsSmooth (u : EllipticTest K) : SmoothScalar E := ⟨u, u.contDiff⟩
@[simp] lemma testAsSmooth_apply (u : EllipticTest K) (x : E) : testAsSmooth K u x = u x := rfl

lemma testAsSmooth_derivative (v : E) (u : EllipticTest K) :
    testAsSmooth K (testDerivative K v u) = SmoothScalar.directional v (testAsSmooth K u) := rfl
lemma testAsSmooth_multiply (b : SmoothScalar E) (u : EllipticTest K) :
    testAsSmooth K (testMultiply K b u) = b * testAsSmooth K u := by
  apply Subtype.ext; ext x; simp only [testAsSmooth_apply, testMultiply_apply, Subalgebra.coe_mul, Pi.mul_apply]
lemma testAsSmooth_sum {η : Type*} (s : Finset η) (u : η → EllipticTest K) :
    testAsSmooth K (∑ i ∈ s, u i) = ∑ i ∈ s, testAsSmooth K (u i) := by
  apply Subtype.ext
  ext x
  simp only [testAsSmooth_apply, SmoothScalar.sum_apply, FunLike.coe_sum, Finset.sum_apply]
lemma testAsSmooth_add (u v : EllipticTest K) :
    testAsSmooth K (u+v) = testAsSmooth K u + testAsSmooth K v := rfl

lemma SmoothScalar.eventuallyEq_directional (v : E) (u w : SmoothScalar E) (x : E)
    (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    (SmoothScalar.directional v u : E → ℝ) =ᶠ[𝓝 x] SmoothScalar.directional v w := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  change fderiv ℝ (u : E → ℝ) y v = fderiv ℝ (w : E → ℝ) y v
  rw [hy]

lemma coefficientElliptic_eq_of_eventuallyEq (a : ι → ι → SmoothScalar E)
    (u w : SmoothScalar E) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    coefficientElliptic e a u x = coefficientElliptic e a w x := by
  simp only [coefficientElliptic, SmoothScalar.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun f : E →L[ℝ] ℝ => f (e i))
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ?_)
  filter_upwards [SmoothScalar.eventuallyEq_directional (e j) u w x h] with y hy
  change a i j y * SmoothScalar.directional (e j) u y = a i j y * SmoothScalar.directional (e j) w y
  rw [hy]

def coefficientSchrodinger (a : ι → ι → SmoothScalar E) (V u : SmoothScalar E) : SmoothScalar E :=
  coefficientElliptic e a u + V*u

lemma coefficientSchrodinger_eq_of_eventuallyEq (a : ι → ι → SmoothScalar E) (V u w : SmoothScalar E)
    (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    coefficientSchrodinger e a V u x = coefficientSchrodinger e a V w x := by
  simp only [coefficientSchrodinger, Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
    coefficientElliptic_eq_of_eventuallyEq e a u w x h, h.eq_of_nhds]

lemma testSchrodinger_asSmooth (a : ι → ι → SmoothScalar E) (V : SmoothScalar E) (u : EllipticTest K) :
    testAsSmooth K (testSchrodinger K e a V u) = coefficientSchrodinger e a V (testAsSmooth K u) := by
  simp only [testSchrodinger, testElliptic, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    testAsSmooth_add, testAsSmooth_sum, testAsSmooth_derivative, testAsSmooth_multiply,
    coefficientElliptic, coefficientSchrodinger]

lemma testSchrodinger_eval_congr (a : ι → ι → SmoothScalar E) (V w : SmoothScalar E)
    (u : EllipticTest K) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    testSchrodinger K e a V u x = coefficientSchrodinger e a V w x := by
  change testAsSmooth K (testSchrodinger K e a V u) x = _
  rw [testSchrodinger_asSmooth]
  exact coefficientSchrodinger_eq_of_eventuallyEq e a V (testAsSmooth K u) w x h

lemma testSchrodinger_zero_of_eventually_zero (a : ι → ι → SmoothScalar E) (V : SmoothScalar E)
    (u : EllipticTest K) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] 0) : testSchrodinger K e a V u x = 0 := by
  rw [testSchrodinger_eval_congr K e a V 0 u x h]
  simp [coefficientSchrodinger, coefficientElliptic]

end YauCounterexamples

end

end OAI
