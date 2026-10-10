import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstTotalReferenceSum
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.BurstTotal
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization SpatialCalculus JointCalculus PeriodicCalculus
variable (A : RoutingData) (ν : ℝ)

def force (q : ℕ) : VectorField 3 := fun t X =>
  lift (residual ν (uncurry (field A ν))) (uncurry (source A ν q)) (t,X)

@[fun_prop] theorem contDiff_force (hν : 0 ≤ ν) (q : ℕ) :
    ContDiff ℝ ∞ (uncurry (force A ν q)) :=
  contDiff_lift (contDiff_residual ν (contDiff_field A ν hν)) (contDiff_source A ν hν q)

theorem force_periodic (hν : 0 ≤ ν) (q : ℕ) (t : ℝ) :
    FactorsThrough (force A ν q t) PeriodicSpace.cover :=
  by
    convert periodic_lift (periodic_residual (field_periodic A ν hν) ν)
      (source_periodic A ν hν q) t using 1
    funext X
    simp only [BurstTotal.force, JointCalculus.lift, JointCalculus.projection_apply,
      liftVelocity, uncurry]

theorem force_finite_derivative_bounds (hν : 0 ≤ ν) (q : ℕ) (T : ℝ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      ‖iteratedFDeriv ℝ d (uncurry (force A ν q)) (t,X)‖ ≤ C :=
  finite_cylinder_bounds (contDiff_force A ν hν q) (force_periodic A ν hν q) T d

theorem field_support (t : ℝ) (X : Coord 2)
    (hX : PeriodicSpace.cover X ∉ PeriodicSpace.cover '' chartSet) : field A ν t X = 0 := by
  unfold field
  apply (tsum_congr _).trans (tsum_zero)
  intro k
  change deriv (clock A ν k) t • periodicPrefix A (k+1) (clock A ν k t) X = 0
  rw [show periodicPrefix A (k+1) (clock A ν k t) X = 0 from
    support_extend (prefix_support A (k+1)) (clock A ν k t) X hX,smul_zero]

theorem source_support (q : ℕ) (c : A.Instruction 0) (hc : A.source 0 c = q)
    (t : ℝ) (X : Coord 2) (hX : PeriodicSpace.cover X ∉ PeriodicSpace.cover '' chartSet) :
    source A ν q t X = 0 := by
  unfold source
  apply (tsum_congr _).trans (tsum_zero)
  intro k
  exact support_extend (BurstBlock.rawSource_support A ν q k c hc) t X hX

theorem force_support (q : ℕ) (c : A.Instruction 0) (hc : A.source 0 c = q)
    (t : ℝ) (X : Coord 3)
    (hX : PeriodicSpace.cover (horizontal X) ∉ PeriodicSpace.cover '' chartSet) :
    force A ν q t X = 0 := by
  have hK := compact_chartSet.image (PeriodicSpace.continuous_cover 2)
  have hr := support_residual hK.isClosed (field_support A ν) ν t (horizontal X) hX
  have hs := source_support A ν q c hc t (horizontal X) hX
  simp only [force,lift,projection_apply,hr,hs,Pi.zero_apply,uncurry_apply_pair]
  ext i
  fin_cases i <;> rfl

theorem force_eq_triangular (hν : 0 ≤ ν) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) (X : Coord 3) :
    force A ν q t X = triangularForce ν (field A ν) (source A ν q) t X := by
  simp only [force,lift,projection_apply,
    residual_eq_horizontalResidual ν (a := field A ν) (contDiff_field A ν hν) ht,
    triangularForce,liftVelocity,uncurry_apply_pair]

@[fun_prop] theorem contDiff_velocity (hν : 0 < ν) (q : ℕ) :
    ContDiff ℝ ∞ (uncurry (velocity A ν hν q)) :=
  by
    convert JointCalculus.contDiff_lift (contDiff_field A ν hν.le)
      (contDiff_scalar A ν hν q) using 1
    funext p
    simp only [uncurry, BurstTotal.velocity, liftVelocity, JointCalculus.lift,
      JointCalculus.projection_apply]

theorem velocity_periodic (hν : 0 < ν) (q : ℕ) (t : ℝ) :
    FactorsThrough (velocity A ν hν q t) PeriodicSpace.cover :=
  periodic_lift (field_periodic A ν hν.le) (scalar_periodic A ν hν q) t

theorem navierStokes (hν : 0 < ν) (q : ℕ) :
    NavierStokes ν (velocity A ν hν q) (fun _ _ => 0) (force A ν q) := by
  have hn := triangular_reduction ν (field A ν) (scalar A ν hν q) (source A ν q)
    (fun t _ => field_divergence A ν hν.le t) (fun _ ht => scalar_equation A ν hν q ht)
    (fun X => congrFun (field_rest A ν hν.le (t := 0) (by norm_num)) X) (scalar_initial A ν hν q)
  refine ⟨?_,hn.2⟩
  intro t ht X i
  rw [force_eq_triangular A ν hν.le q ht]
  exact hn.1 t ht X i

end VelocityDetection.BurstTotal
end

end OAI
