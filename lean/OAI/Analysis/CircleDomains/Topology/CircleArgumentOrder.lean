import OAI.Analysis.CircleDomains.Topology.BoundaryOrderExtension
import OAI.Analysis.CircleDomains.Topology.PhysicalCollarCoordinates

namespace OAI

/-! Normalize the argument of the actual centered collar boundary by its
first value. Its real lift runs once around the circle, in one of the two
orientations; no differentiability of the centered Jordan map is assumed. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem normalizedArgument_injective_on_unit_sphere {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (h : normalizedArgument z = normalizedArgument w) : z = w := by
  apply Complex.ext_norm_arg
  · exact hz.trans hw.symm
  · apply Complex.arg_coe_angle_eq_iff.mp
    exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective h

 theorem normalizedArgument_div {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    normalizedArgument (z / w) = normalizedArgument z - normalizedArgument w := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (z / w) : Real.Angle) = e (Complex.arg z) - e (Complex.arg w)
  rw [Complex.arg_div_coe_angle hz hw, e.map_sub]

 theorem exists_ordered_argument_lift
    (z : ℝ → ℂ) (hz : Continuous z) (hnorm : ∀ t, ‖z t‖ = 1)
    (hperiod : Function.Periodic z 1) (hinj : InjOn z (Ico (0 : ℝ) 1)) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧
      (∀ t, (q t : UnitAddCircle) = normalizedArgument (z t / z 0)) ∧
      ((StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
        (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1)) := by
  have hne (t : ℝ) : z t ≠ 0 := by
    intro h
    have hn := hnorm t
    rw [h, norm_zero] at hn
    norm_num at hn
  let g : ℝ → UnitAddCircle := fun t => normalizedArgument (z t) - normalizedArgument (z 0)
  have hc : Continuous (fun t : ℝ => normalizedArgument (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_normalizedArgument (hne t)).comp hz.continuousAt
  have hcont : Continuous g := hc.sub continuous_const
  have hgperiod : Function.Periodic g 1 := fun t => by dsimp only [g]; rw [hperiod t]
  have hgi : InjOn g (Ico (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact hinj hx hy (normalizedArgument_injective_on_unit_sphere (hnorm x) (hnorm y)
      (by simpa only [g, sub_left_inj] using heq))
  obtain ⟨q, hq, hq0, hqp, hord⟩ := exists_ordered_circle_boundary_lift g hcont hgperiod
    (sub_self _) hgi
  refine ⟨q, hq, hq0, ?_, hord⟩
  intro t
  exact (hqp t).trans (normalizedArgument_div (hne t) (hne 0)).symm

 theorem exists_ordered_centered_collar_boundary_lift
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {b : ℂ} (hb : b ∈ jordanInterior H)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate H (b : Sphere))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧
      (∀ t, (q t : UnitAddCircle) = normalizedArgument
        (F (C.curve 0 t : Sphere) / F (C.curve 0 0 : Sphere))) ∧
      ((StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
        (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1)) := by
  have hpar := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hbs : (b : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H := ⟨b, hb, rfl⟩
  have hfront (t : ℝ) : (C.curve 0 t : Sphere) ∈
      frontier (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [frontier_sphere_image_jordanInterior]
    have hh := hpar.mem_frontier t
    rw [C.disk_zero] at hh
    exact ⟨_, hh, rfl⟩
  apply exists_ordered_argument_lift (fun t => F (C.curve 0 t : Sphere))
    (F.continuous.comp (OnePoint.continuous_coe.comp hpar.smooth.continuous))
  · intro t
    rw [hF (frontier_subset_closure (hfront t))]
    exact centeredJordanCoordinate_norm_boundary H hbs (hfront t)
  · exact hpar.periodic.comp (fun z : ℂ => F (z : Sphere))
  · intro x hx y hy heq
    apply hpar.injective hx hy
    apply OnePoint.coe_injective
    apply centeredJordanCoordinate_injOn H hbs
      (frontier_subset_closure (hfront x)) (frontier_subset_closure (hfront y))
    simpa only [← hF (frontier_subset_closure (hfront x)),
      ← hF (frontier_subset_closure (hfront y))] using heq

end CircleDomainRigidity

end

end OAI
