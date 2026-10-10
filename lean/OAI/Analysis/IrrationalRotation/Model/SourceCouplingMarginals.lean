import OAI.Analysis.IrrationalRotation.Model.BlockProductCoupling
import OAI.Analysis.IrrationalRotation.Model.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Model.OneCoordinateConditional
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

def sourceBlocks (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) : Parameters :=
  ofBlocks m sourceKappa a b
    (by intro s; unfold sourceKappa; positivity)
    (by
      intro s
      unfold sourceKappa
      apply (div_le_iff₀ (by positivity : 0 < 100 * ((s : ℝ) + 1))).2
      nlinarith [Nat.cast_nonneg (α := ℝ) s])
    hm ha ha' hb hb' e tag

structure SourceMarginalProperties (P : Parameters) (H : ℝ) : Prop where
  [law_probability : IsProbabilityMeasure (law P)]
  H_positive : 0 < H
  probability : IsProbabilityMeasure (circlePairLaw P)
  ordered : ∀ᵐ xy ∂circlePairLaw P, ProductModel.Ordered xy.1 xy.2
  representatives : ∀ᵐ ω ∂law P,
    realEndpoint (circleLeftEndpoint ω) = leftEndpoint ω ∧
      realEndpoint (circleRightEndpoint ω) = rightEndpoint ω
  coordinate_densities : ∀ (side : Bool) (i : ℕ),
    (coordinateLaw P i).map (fun z => if side then z.2.2 else z.2.1) =
      OneCoordinateCoupling.baseLaw.withDensity
        (fun x => ENNReal.ofReal (marginalDensity P side i x))
  coordinate_bound : ∀ (side : Bool) (i : ℕ) (x : ℝ),
    0 ≤ marginalDensity P side i x ∧ marginalDensity P side i x ≤ 10
  hybrid_densities : ∀ ε : ℕ → Bool,
    ∃ g : ProductModel.Base → ℝ, MemLp g 2 ProductModel.baseMeasure ∧
      (0 ≤ᵐ[ProductModel.baseMeasure] g) ∧
      (∫ x, g x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm g 2 ProductModel.baseMeasure ≤ ENNReal.ofReal H ∧
      (law P).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (g x))
  hybrid_mass_bound : ∀ (ε : ℕ → Bool) (A : Set ProductModel.Base), MeasurableSet A →
    ((law P).map (circleHybridEndpoint ε)).real A ≤
      H * Real.sqrt (ProductModel.baseMeasure.real A)
  right_kernel : condDistrib rightEndpoint leftEndpoint (law P)
    =ᵐ[(law P).map leftEndpoint] fun x => Measure.infinitePi
      (fun i => OneCoordinateCoupling.rightGivenLeft
        (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (x i))
  left_kernel : condDistrib leftEndpoint rightEndpoint (law P)
    =ᵐ[(law P).map rightEndpoint] fun y => Measure.infinitePi
      (fun i => OneCoordinateCoupling.leftGivenRight
        (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) (y i))
  right_independent : ∀ᵐ x ∂(law P).map leftEndpoint,
    iIndepFun (fun i (y : Endpoint) => y i) (condDistrib rightEndpoint leftEndpoint (law P) x)
  left_independent : ∀ᵐ y ∂(law P).map rightEndpoint,
    iIndepFun (fun i (x : Endpoint) => x i) (condDistrib leftEndpoint rightEndpoint (law P) y)
  right_crossing : ∀ᵐ x ∂(law P).map leftEndpoint, ∀ (i : ℕ) (w u : ℝ),
    (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → x i < u →
    CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
      (condDistrib rightEndpoint leftEndpoint (law P) x).real
        {y : Endpoint | x i < u ∧ u ≤ y i}
  left_crossing : ∀ᵐ y ∂(law P).map rightEndpoint, ∀ (i : ℕ) (w u : ℝ),
    (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → u ≤ y i →
    CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
      (condDistrib leftEndpoint rightEndpoint (law P) y).real
        {x : Endpoint | x i < u ∧ u ≤ y i}

end Invariant233.OrderedProductCoupling

end

end OAI
