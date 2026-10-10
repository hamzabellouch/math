import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightTests
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitL2Marginals
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTrimming

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

def orientedAverage (endpoint : Bool) (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (x : Base) : ℝ :=
  (N.card : ℝ)⁻¹ * ∑ n ∈ N, ∏ i ∈ D,
    testedCoordinateWeight endpoint I h α i univ univ
      (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))

@[simp] theorem rectangle_univ (D : Finset ℕ) :
    rectangle D (fun _ => univ) (fun _ => univ) = univ := by
  ext x
  simp only [rectangle, mem_ofPred_eq, mem_univ, and_self, implies_true]

theorem orientedAverage_first (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (x : Base) :
    orientedAverage false D I N h α θ x =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitWeight D I h α θ n x := by
  simp only [orientedAverage, testedCoordinateWeight, Bool.false_eq_true,
    ite_false, Set.indicator_univ, mul_one, orbitWeight]

theorem orientedAverage_second (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (y : Base) :
    orientedAverage true D I N h α θ y =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N,
        orbitWeight D I h α θ n (rotationIterate θ (-(n : ℤ)) y) := by
  unfold orientedAverage
  apply congrArg ((N.card : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [rectangle_univ, Set.indicator_univ] using
    second_tested_product_eq D I h α θ n (fun _ => univ) (fun _ => univ) y

theorem hasUniformL2Marginals_of_oriented_bounds
    (θ : ℕ → ℝ) (I : Finset ℕ) (D N : ℕ → Finset ℕ) (h α : ℕ → ℝ)
    (hh : ∀ l, 0 < h l) (hα : ∀ l, 0 < α l)
    {H : ℝ} (hH : 0 ≤ H)
    (hfirst : ∀ l, eLpNorm (orientedAverage false (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H)
    (hsecond : ∀ l, eLpNorm (orientedAverage true (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H) :
    HasUniformL2Marginals (fun l => TailTrimming.orbitAverageMeasure θ (N l)
      (fun n x => ENNReal.ofReal (orbitWeight (D l) I (h l) (α l) θ n x))) := by
  apply TailTrimming.hasUniformL2Marginals_of_average_bounds θ N
    (fun l => orbitWeight (D l) I (h l) (α l) θ)
    (fun l n _ => measurable_orbitWeight (D l) I (h l) (α l) θ n)
    (fun l n _ x => (orbitWeight_bounds (D l) I (hh l) (hα l) θ n x).1) hH
  · intro l
    simpa only [funext (orientedAverage_first (D l) I (N l) (h l) (α l) θ)] using hfirst l
  · intro l
    simpa only [funext (orientedAverage_second (D l) I (N l) (h l) (α l) θ)] using hsecond l

theorem orderedOrbitSampling_of_oriented_estimates
    (θ : ℕ → ℝ) (I : Finset ℕ) (hθ : ∀ i, 0 ≤ θ i)
    (D N : ℕ → Finset ℕ) (M : ℕ → ℕ) (h α : ℕ → ℝ)
    (hh : ∀ l, 0 < h l) (hh1 : ∀ l, h l ≤ 1) (hα : ∀ l, 0 < α l)
    (hN : ∀ l, ∀ n ∈ N l, 0 < n) (hM : ∀ l, ∀ n ∈ N l, n ≤ M l)
    {H : ℝ} (hH : 0 ≤ H)
    (hfirst : ∀ l, eLpNorm (orientedAverage false (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H)
    (hsecond : ∀ l, eLpNorm (orientedAverage true (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H)
    (hweak : WeaklyConverges (fun l => TailTrimming.orbitAverageMeasure θ (N l)
      (fun n x => ENNReal.ofReal (orbitWeight (D l) I (h l) (α l) θ n x)))
      (triangularLaw I))
    (htail : Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i)) atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  have hL2 := hasUniformL2Marginals_of_oriented_bounds θ I D N h α hh hα hH hfirst hsecond
  apply TailTrimming.orderedOrbitSampling_of_prefix_samples θ I hθ D N M
    (fun l n x => ENNReal.ofReal (prefixWeight (D l) I (h l) (α l) θ n x))
    (fun l n _ => (measurable_prefixWeight (D l) I (h l) (α l) θ n).ennreal_ofReal)
    hN hM
  · intro l n hn
    simpa only [prefixWeight_restrict] using
      orbitWeight_ae_prefix_order (D l) I (hh1 l) θ n
  · simpa only [prefixWeight_restrict] using hL2
  · simpa only [prefixWeight_restrict] using hweak
  · exact htail

end Invariant233.ProductModel.SamplingWeights

end

end OAI
