import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayBounds
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculusHorizontalLinear

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses UniformDerivatives JointCalculus SmoothProfiles
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

def force (p : Coord 2) : VectorField 3 := fun t X =>
  lift (residual ν (uncurry (field hb table terminal ν m))) (uncurry (impulse p)) (t, X)

@[fun_prop] theorem contDiff_force (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (force hb table terminal ν m p)) :=
  contDiff_lift (contDiff_residual ν (contDiff_field hb table terminal ν m hν))
    (contDiff_impulse p)

theorem force_uniformly_bounded (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (p : Coord 2) :
    Bounded (fun _ : Unit => uncurry (force hb table terminal ν m p)) := by
  apply bounded_lift (contDiff_residual ν (contDiff_field hb table terminal ν m hν))
    (contDiff_impulse p)
  · exact Bounded.residual ν (contDiff_field hb table terminal ν m hν)
      (field_uniformly_bounded hb table terminal ν m hν hm hdir hin)
  · exact compact (contDiff_impulse p) (compactSupport_impulse p)

theorem force_vertical_independent (p : Coord 2) (t : ℝ) (X : Coord 3) (z : ℝ) :
    force hb table terminal ν m p t (update X 2 z) = force hb table terminal ν m p t X := by
  simp only [force, lift, projection_apply, horizontal_update_two]

theorem force_eq_triangular (hν : 0 < ν) (p : Coord 2) {t : ℝ} (ht : 0 ≤ t) (X : Coord 3) :
    force hb table terminal ν m p t X =
      triangularForce ν (field hb table terminal ν m) (impulse p) t X := by
  simp only [force, lift, projection_apply,
    residual_eq_horizontalResidual ν (a := field hb table terminal ν m) (contDiff_field hb table terminal ν m hν) ht,
    triangularForce, liftVelocity, uncurry_apply_pair]

theorem force_finiteCylinderSupport (hν : 0 < ν) (p : Coord 2) (T : ℝ) :
    ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t, 0 ≤ t → t ≤ T →
      ∀ X : Coord 3, horizontal X ∉ K → force hb table terminal ν m p t X = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt T
  let a : ℝ × Coord 2 → Coord 2 :=
    fun q => ∑ n ∈ Finset.range Q, stage hb table terminal ν m n q.1 q.2
  have ha : HasCompactSupport a := by
    simpa only [Finset.sum_fn, a] using HasCompactSupport.finset_sum
      (fun n (_ : n ∈ Finset.range Q) => compactSupport_stage hb table terminal ν m hν n)
  let K : Set (Coord 2) := (Prod.snd '' tsupport (residual ν a)) ∪ tsupport (spatialPulse p)
  refine ⟨K, ((compactSupport_residual ν ha).image continuous_snd).union
    (compactSupport_spatialPulse p), ?_⟩
  intro t ht0 ht X hX
  have hev : uncurry (field hb table terminal ν m) =ᶠ[𝓝 (t, horizontal X)] a := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds (ht.trans_lt hQ)] with q hq
    exact field_eq_finite hb table terminal ν m hν hq q.2
  have hr : residual ν a (t, horizontal X) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hX (Or.inl ⟨(t, horizontal X), h, rfl⟩)
  have hg : spatialPulse p (horizontal X) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hX (Or.inr h)
  simp only [force, lift, projection_apply,
    (eventuallyEq_residual ν hev).eq_of_nhds, hr, Pi.zero_apply, uncurry_apply_pair, impulse, hg,
    mul_zero]
  ext i
  fin_cases i <;> rfl

theorem force_NavierStokes (hν : 0 < ν) (p : Coord 2) (ρ : ScalarField 2)
    (hρ : ∀ t, 0 ≤ t → ∀ X, timeD ρ t X + advection (field hb table terminal ν m) ρ t X =
      ν * laplacian ρ t X + impulse p t X) (hρ0 : ∀ X, ρ 0 X = 0) :
    NavierStokes ν (liftVelocity (field hb table terminal ν m) ρ) 0
      (force hb table terminal ν m p) := by
  have hn := triangular_reduction ν (field hb table terminal ν m) ρ (impulse p)
    (fun t _ => divergence_field hb table terminal ν m hν t) hρ
    (field_at_rest hb table terminal ν m hν (by norm_num)) hρ0
  refine ⟨?_, hn.2⟩
  intro t ht X i
  rw [force_eq_triangular hb table terminal ν m hν p ht]
  exact hn.1 t ht X i

end VelocityDetection.ExpandingArray
end

end OAI
