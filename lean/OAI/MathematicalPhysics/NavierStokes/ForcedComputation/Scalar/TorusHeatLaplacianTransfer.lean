import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatTimeDerivative
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatIntegrationByParts
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TorusConvolution

namespace OAI

/-! Transfer of the time derivative to the Laplacian of the initial data. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff BigOperators

private theorem reflected_spatialD {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (j : Fin 2) :
    spatialD j (fun y => f (x-y)) = fun y => -spatialD j f (x-y) := by
  funext y
  have hm : HasFDerivAt (fun z : Plane => x-z) (-(ContinuousLinearMap.id ℝ Plane)) y := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y) using 1
    simp only [zero_sub]
  have h := (hf.differentiable (by simp) (x-y)).hasFDerivAt.comp y hm
  change HasFDerivAt (fun y => f (x-y)) _ y at h
  rw [spatialD, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg, spatialD]

private theorem reflected_spatialD_twice {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (j : Fin 2) :
    spatialD j (spatialD j (fun y => f (x-y))) =
      fun y => spatialD j (spatialD j f) (x-y) := by
  rw [reflected_spatialD hf]
  funext y
  rw [spatialD, fderiv_fun_neg, neg_apply]
  change -spatialD j (fun z => spatialD j f (x-z)) y = _
  rw [reflected_spatialD (spatialD_smooth j hf)]
  exact neg_neg _

private theorem reflected_periodic {f : Plane → ℝ} (hp : PlanePeriodic f) (x : Plane) :
    PlanePeriodic (fun y => f (x-y)) := by
  intro y n
  have he : x-(y+fun j => (n j : ℝ)) = (x-y)+fun j => ((-n j : ℤ) : ℝ) := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_neg]
    ring
  change f (x-(y+fun j => (n j : ℝ))) = f (x-y)
  rw [he, hp (x-y) (fun j => -n j)]

theorem heatLaplacianIntegral_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) {t : ℝ} (ht : 0 < t) (x : Plane) :
    heatLaplacianIntegral g t x = torusHeatEvolution (scalarLaplacian g) t x := by
  have hk : ContDiff ℝ ∞ (torusHeatKernel t) := by
    have h := torusHeatKernel_smooth_positive.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (show MapsTo (fun y : Plane => (t,y)) univ (Ioi (0 : ℝ) ×ˢ univ) from
        fun _ _ => ⟨ht, mem_univ _⟩)
    simpa only [Function.comp_def, id_eq, contDiffOn_univ] using h
  have hkr : ContDiff ℝ ∞ (fun y : Plane => torusHeatKernel t (x-y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hpr := reflected_periodic (torusHeatKernel_periodic ht) x
  have hj (j : Fin 2) :
      (∫ y in Icc (0 : Plane) (fun _ => 1),
        spatialD j (spatialD j (torusHeatKernel t)) (x-y) * g y) =
      ∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x-y) * spatialD j (spatialD j g) y := by
    have h := periodic_integral_mul_spatialD_twice hkr hg hpr hp j
    rw [reflected_spatialD_twice hk] at h
    exact h.symm
  have hi₁ (j : Fin 2) : IntegrableOn (fun y : Plane =>
      spatialD j (spatialD j (torusHeatKernel t)) (x-y) * g y)
      (Icc (0 : Plane) (fun _ => 1)) :=
    (((spatialD_smooth j (spatialD_smooth j hk)).comp
      (contDiff_const.sub contDiff_id)).continuous.mul hg.continuous).integrableOn_Icc
  have hi₂ (j : Fin 2) : IntegrableOn (fun y : Plane =>
      torusHeatKernel t (x-y) * spatialD j (spatialD j g) y)
      (Icc (0 : Plane) (fun _ => 1)) :=
    (hkr.continuous.mul (spatialD_smooth j (spatialD_smooth j hg)).continuous).integrableOn_Icc
  rw [heatLaplacianIntegral, torusHeatEvolution, ite_eq_right (not_le.mpr ht)]
  simp only [scalarLaplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => hi₁ j),
    integral_finsetSum Finset.univ (fun j _ => hi₂ j)]
  exact Finset.sum_congr rfl (fun j _ => hj j)

theorem torusHeatEvolution_time_data {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) {t : ℝ} (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => torusHeatEvolution g s x)
      (torusHeatEvolution (scalarLaplacian g) t x) t := by
  rw [← heatLaplacianIntegral_eq hg hp ht x]
  exact torusHeatEvolution_hasDerivAt hg.continuous ht x

theorem torusHeatEvolution_add_direct {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (t : ℝ) (x : Plane) :
    torusHeatEvolution (f+g) t x = torusHeatEvolution f t x + torusHeatEvolution g t x := by
  by_cases ht : t ≤ 0
  · simp only [torusHeatEvolution, ite_eq_left ht, Pi.add_apply]
  · have hk : Continuous (fun y : Plane => torusHeatKernel t (x-y)) :=
      (torusHeatKernel_continuous (lt_of_not_ge ht)).comp (continuous_const.sub continuous_id)
    simp only [torusHeatEvolution, ite_eq_right ht, Pi.add_apply, mul_add]
    exact integral_add (hk.mul hf).integrableOn_Icc (hk.mul hg).integrableOn_Icc

theorem torusHeatEvolution_laplacian {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) (t : ℝ) :
    scalarLaplacian (torusHeatEvolution g t) = torusHeatEvolution (scalarLaplacian g) t := by
  have hj (j : Fin 2) : spatialD j (spatialD j (torusHeatEvolution g t)) =
      torusHeatEvolution (spatialD j (spatialD j g)) t := by
    rw [torusHeatEvolution_spatialD hg hp,
      torusHeatEvolution_spatialD (spatialD_smooth j hg) (spatialD_periodic hg hp j)]
  have he : scalarLaplacian g = spatialD 0 (spatialD 0 g) + spatialD 1 (spatialD 1 g) := by
    funext x
    simp only [scalarLaplacian, Fin.sum_univ_two, Pi.add_apply]
  funext x
  rw [he, torusHeatEvolution_add_direct
    (spatialD_smooth 0 (spatialD_smooth 0 hg)).continuous
    (spatialD_smooth 1 (spatialD_smooth 1 hg)).continuous]
  simp only [scalarLaplacian, Fin.sum_univ_two, hj]

end ForcedComputation.VelocityDetector

end

end OAI
