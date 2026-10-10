import OAI.Geometry.IsometricImmersion.Calculus.QuotientLowBounds
import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftCoefficients

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {M c : ℝ}

theorem hessianQuotient_coordinate_bound_through_three
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hH : ∀ i j : Fin 2, ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
      |iteratedCoordPartial ds (fun x => covHessian g z x i j) p| ≤ M)
    (hden : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
        |iteratedCoordPartial ds (hessianQuotient g z) p| ≤ LowQuotient.boundThroughThree M c := by
  have hxy := covHessian_contDiffOn hg hU hz 0 1
  have hyy := covHessian_contDiffOn hg hU hz 1 1
  refine ⟨hessianQuotient_contDiffOn hg hU hz (LowQuotient.denominator_ne_zero hc hden), ?_⟩
  intro ds hlen p hp
  exact LowQuotient.quotient_bound_through_three hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden ds hlen hp

theorem hessianQuotient_coordinate_bounds_by_order
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hH : ∀ i j : Fin 2, ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
      |iteratedCoordPartial ds (fun x => covHessian g z x i j) p| ≤ M)
    (hden : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|)
    {p : Coord} (hp : p ∈ U) :
    |hessianQuotient g z p| ≤ LowQuotient.bound0 M c ∧
    (∀ i : Fin 2, |coordPartial i (hessianQuotient g z) p| ≤ LowQuotient.bound1 M c) ∧
    (∀ i j : Fin 2, |coordPartial i (coordPartial j (hessianQuotient g z)) p| ≤ LowQuotient.bound2 M c) ∧
    (∀ i j k : Fin 2, |coordPartial i (coordPartial j (coordPartial k (hessianQuotient g z))) p| ≤
      LowQuotient.bound3 M c) := by
  have hxy := covHessian_contDiffOn hg hU hz 0 1
  have hyy := covHessian_contDiffOn hg hU hz 1 1
  refine ⟨LowQuotient.quotient_bound_zero hM hc (hH 0 1 [] (by norm_num)) hden hp, ?_, ?_, ?_⟩
  · intro i
    exact LowQuotient.quotient_bound_one hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden hp i
  · intro i j
    exact LowQuotient.quotient_bound_two hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden hp i j
  · intro i j k
    exact LowQuotient.quotient_bound_three hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden hp i j k

end SmoothLocal.Geometry

end

end OAI
