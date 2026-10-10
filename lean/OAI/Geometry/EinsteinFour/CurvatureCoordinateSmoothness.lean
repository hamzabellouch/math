import OAI.Geometry.EinsteinFour.ChartMetricSmoothness
import OAI.Geometry.EinsteinFour.WeylDerivative

namespace OAI

/-! Local regularity of the actual curvature and its coordinate covariant
derivatives, on the nonsingular part of a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem curvatureComponent_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (l i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => curvatureComponent g c w l i j k) z := by
  have hc := christoffel_contDiffAt g c z hz hdet
  have hd (r s t u : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => partialDeriv (fun v => christoffel g c v r s t) u w) z :=
    ((hc r s t).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  unfold curvatureComponent
  apply ((hd l j k i).sub (hd l i k j)).add
  apply ContDiffAt.sum
  intro p _
  exact ((hc l i p).mul (hc p j k)).sub ((hc l j p).mul (hc p i k))

theorem curvatureCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => curvatureCoordinates g c w a) z := by
  unfold curvatureCoordinates
  apply ContDiffAt.sum
  intro l _
  exact (metricInChart_contDiffAt g c z hz l (a 3)).mul
    (curvatureComponent_contDiffAt g c z hz hdet l (a 0) (a 1) (a 2))

theorem unitCurvatureCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => unitCurvatureCoordinates g c w a) z := by
  have h := metricInChart_contDiffAt g c z hz
  exact ((h (a 1) (a 2)).mul (h (a 0) (a 3))).sub
    ((h (a 0) (a 2)).mul (h (a 1) (a 3)))

theorem normalizedWeylCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => normalizedWeylCoordinates g c w a) z :=
  (curvatureCoordinates_contDiffAt g c z hz hdet a).sub
    (unitCurvatureCoordinates_contDiffAt g c z hz a)

theorem covariantDerivative_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) {n : ℕ}
    (T : FourSpace → CovariantCoordinates n)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin (n + 1) → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => covariantDerivative g c T w a) z := by
  unfold covariantDerivative
  apply (((hT _).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro b _
  exact (christoffel_contDiffAt g c z hz hdet b (a 0) (a i.succ)).mul (hT _)

/-- Linearity is proved for differentiable coordinate tensors, so it also
applies to the actual curvature fields on a metric chart. -/
theorem covariantDerivative_sub (g : SmoothMetric M) (c : M) (z : FourSpace)
    {n : ℕ} (S T : FourSpace → CovariantCoordinates n)
    (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) :
    covariantDerivative g c (fun w => S w - T w) z =
      covariantDerivative g c S z - covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => S w (fun i => a i.succ) -
        T w (fun i => a i.succ)) (a 0) z =
      partialDeriv (fun w => S w (fun i => a i.succ)) (a 0) z -
        partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector (a 0)))
      (fderiv_fun_sub (hS _) (hT _))
  simp only [covariantDerivative, Pi.sub_apply, hd, mul_sub,
    Finset.sum_sub_distrib]
  ring

theorem covariantDerivative_congr (g : SmoothMetric M) (c : M) {z : FourSpace}
    {n : ℕ} {S T : FourSpace → CovariantCoordinates n}
    (h : S =ᶠ[nhds z] T) :
    covariantDerivative g c S z = covariantDerivative g c T z := by
  funext a
  have hv : S z = T z := h.eq_of_nhds
  have hd : (fun w => S w (fun i => a i.succ)) =ᶠ[nhds z]
      (fun w => T w (fun i => a i.succ)) :=
    h.mono fun w hw => congrFun hw _
  simp only [covariantDerivative, partialDeriv, hd.fderiv_eq, hv]

end
end PositiveEinsteinFour.Geometry

end OAI
