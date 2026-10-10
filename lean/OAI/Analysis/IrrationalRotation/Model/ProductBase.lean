import OAI.Analysis.IrrationalRotation.Model.Analytic
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233

def circleRepresentative (x : Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x).val

instance circleMeasure_probability : IsProbabilityMeasure circleMeasure := by
  constructor
  simp [circleMeasure, Circle, AddCircle.measure_univ]

namespace ProductModel

abbrev Base := ℕ → Circle

def baseMeasure : Measure Base := Measure.infinitePi (fun _ : ℕ => circleMeasure)

instance baseMeasure_probability : IsProbabilityMeasure baseMeasure := by
  unfold baseMeasure
  infer_instance

def Ordered (x y : Base) : Prop :=
  ∀ i, circleRepresentative (x i) ≤ circleRepresentative (y i)

def rotation (θ : ℕ → ℝ) (x : Base) : Base :=
  fun i => x i + (θ i : Circle)

def rotationIterate (θ : ℕ → ℝ) (k : ℤ) (x : Base) : Base :=
  fun i => x i + ((k : ℝ) * θ i : ℝ)

def logarithmicCost (θ c : ℕ → ℝ) (x : Base) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℤ))

def weight (θ c : ℕ → ℝ) (x : Base) : ℝ :=
  (EReal.exp (-(logarithmicCost θ c x : EReal))).toReal

def JointlyRationallyIndependent (θ : ℕ → ℝ) : Prop :=
  LinearIndependent ℚ (fun i : Option ℕ => i.elim 1 θ)

def AdmissibleAnglesAndCosts (θ c : ℕ → ℝ) : Prop :=
  (∀ i, 0 < θ i ∧ θ i < 1 ∧ 0 < c i) ∧
    Summable θ ∧ JointlyRationallyIndependent θ

abbrev Fiber := @lp ℤ (fun _ => ℂ) (fun _ => Complex.instNormedAddCommGroup) 2
abbrev Hilbert :=
  @MeasureTheory.Lp Base Fiber MeasurableSpace.pi
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    2 baseMeasure

end ProductModel
end Invariant233

end

end OAI
