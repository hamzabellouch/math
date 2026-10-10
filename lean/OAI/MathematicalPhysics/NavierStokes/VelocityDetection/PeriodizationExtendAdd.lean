import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodizationSupportDAlong

namespace OAI

noncomputable section
namespace VelocityDetection.Periodization
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus PeriodicSpace
variable {n : ℕ}

theorem extend_add {f g : ScalarField n} {C : ℝ}
    (hf : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C)
    (hg : ∀ t X, g t X ≠ 0 → ∀ i, |X i| ≤ C) :
    extend (fun t X => f t X+g t X) = fun t X => extend f t X+extend g t X := by
  funext t X
  obtain ⟨N,hN⟩ := exists_nat_gt (‖X‖+C)
  have hs : ∀ t X, f t X+g t X ≠ 0 → ∀ i, |X i| ≤ C := by
    intro t X h
    by_cases hf0 : f t X = 0
    · exact hg t X (by simpa [hf0] using h)
    · exact hf t X hf0
  rw [extend_finite hs hN,extend_finite hf hN,extend_finite hg hN,Finset.sum_add_distrib]

theorem extend_time_mul (a : ℝ → ℝ) (f : ScalarField n) :
    extend (fun t X => a t*f t X) = fun t X => a t*extend f t X := by
  funext t X
  simp only [extend,tsum_mul_left]

theorem advection_extend {f : ScalarField n} {C : ℝ} (a : VectorField n)
    (hp : ∀ t, FactorsThrough (a t) cover)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C) :
    advection a (extend f) = extend (advection a f) := by
  have hcoeff (i : Fin n) : ∀ t, FactorsThrough (fun X => a t X i) cover := by
    intro t X Y hXY
    exact congrFun (hp t hXY) i
  have hsupport : ∀ i : Fin n, ∀ t X, a t X i*spatialD i f t X ≠ 0 → ∀ j, |X j| ≤ C := by
    intro i t X h
    exact boundedSupport_spatialD hf hs i t X (right_ne_zero_of_mul h)
  funext t X
  unfold advection
  simp_rw [spatialD_extend hf hs]
  rw [congrFun (congrFun (extend_sum Finset.univ
    (fun i => fun t X => a t X i*spatialD i f t X) (fun i _ => hsupport i)) t) X]
  exact Finset.sum_congr rfl (fun i _ =>
    congrFun (congrFun (extend_periodic_mul (fun t X => a t X i) (spatialD i f) (hcoeff i)) t) X |>.symm)

theorem transport_extend {f g : ScalarField n} {C : ℝ} (a : VectorField n)
    (hp : ∀ t, FactorsThrough (a t) cover)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C)
    (heq : ∀ t X, deriv (fun s => f s X) t + advection a f t X = g t X) :
    ∀ t X, deriv (fun s => extend f s X) t + advection a (extend f) t X = extend g t X := by
  have hd : ∀ t X, deriv (fun s => f s X) t ≠ 0 → ∀ i, |X i| ≤ C := by
    simp_rw [deriv_eq_dAlong hf]
    exact boundedSupport_dAlong hs (1,0)
  have ha : ∀ t X, advection a f t X ≠ 0 → ∀ i, |X i| ≤ C := by
    intro t X h
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact boundedSupport_spatialD hf hs i t X (right_ne_zero_of_mul hi)
  intro t X
  rw [deriv_extend hf hs,advection_extend a hp hf hs,
    ← congrFun (congrFun (extend_add hd ha) t) X]
  congr 1
  exact funext (fun t => funext (heq t))

end VelocityDetection.Periodization
end

end OAI
