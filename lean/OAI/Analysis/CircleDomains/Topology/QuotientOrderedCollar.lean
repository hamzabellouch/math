import OAI.Analysis.CircleDomains.Topology.OrderedCollarLift
import OAI.Analysis.CircleDomains.Topology.PuncturedPhysicalCollar

namespace OAI

/-! The ordered collar construction for the actual component quotient.
The physical collar stays smooth although the quotient Jordan coordinate
need only be continuous. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem frontier_quotient_jordan_collar
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H J : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J) :
    frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
  rw [← hregion]
  rw [frontier_image_of_saturated_open π hπ
    (((↑) : ℂ → Sphere) '' jordanInterior H)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
    (isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr H hboundary)
    (hclosed _ isClosed_closure)
    (preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary),
    frontier_sphere_image_jordanInterior]

 theorem exists_quotient_ordered_collar_lift
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H J : ℂ ≃ₜ ℂ) (C : RegularJordanInwardCollar H)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J))) :
    Nonempty (OrderedCollarLift C (F.comp ⟨π, hπ⟩)) := by
  let P : C(Sphere, ℂ) := F.comp ⟨π, hπ⟩
  have hfront := frontier_quotient_jordan_collar G π hπ hclosed hsurj hr H J hboundary hregion
  have hcl (z : ℂ) (hz : z ∈ closure (jordanInterior H)) :
      π (z : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [← hregion]
    apply image_closure_subset_closure_image hπ
    refine ⟨(z : Sphere), ?_, rfl⟩
    rw [closure_sphere_image_jordanInterior]
    exact ⟨z, hz, rfl⟩
  have hf (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) :
      π (z : Sphere) ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [hfront]
    exact ⟨(z : Sphere), ⟨z, hz, rfl⟩, rfl⟩
  have hn (z : ℂ) (hz : z ∈ closure (jordanInterior H)) : ‖P (z : Sphere)‖ ≤ 1 := by
    change ‖F (π (z : Sphere))‖ ≤ 1
    rw [hF (hcl z hz)]
    exact centeredJordanCoordinate_norm_le J hb (hcl z hz)
  have hbn (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) : ‖P (z : Sphere)‖ = 1 := by
    change ‖F (π (z : Sphere))‖ = 1
    rw [hF (frontier_subset_closure (hf z hz))]
    exact centeredJordanCoordinate_norm_boundary J hb (hf z hz)
  have hb0 (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) : P (z : Sphere) ≠ 0 := by
    intro he
    have hh := hbn z hz
    rw [he, norm_zero] at hh
    norm_num at hh
  have hpar := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hparfront (t : ℝ) : C.curve 0 t ∈ frontier (jordanInterior H) := by
    simpa only [C.disk_zero] using hpar.mem_frontier t
  have hnorm (t : ℝ) : ‖P (C.curve 0 t : Sphere)‖ = 1 := hbn _ (hparfront t)
  have hi : InjOn (fun t => P (C.curve 0 t : Sphere)) (Ico (0 : ℝ) 1) := by
    intro s hs t ht he
    have hp : π (C.curve 0 s : Sphere) = π (C.curve 0 t : Sphere) := by
      apply centeredJordanCoordinate_injOn J hb
        (frontier_subset_closure (hf _ (hparfront s)))
        (frontier_subset_closure (hf _ (hparfront t)))
      change F (π (C.curve 0 s : Sphere)) = F (π (C.curve 0 t : Sphere)) at he
      rwa [hF (frontier_subset_closure (hf _ (hparfront s))),
        hF (frontier_subset_closure (hf _ (hparfront t)))] at he
    rcases (hr _ _).mp hp with h | h
    · exact hpar.injective hs ht (OnePoint.coe_injective h)
    · exact (h.1 (hboundary _ (hparfront s))).elim
  have hstart : ∃ a, P (C.curve 0 a : Sphere) = 1 := by
    have hx := centeredJordanBoundary_mem_frontier J hb (0 : UnitAddCircle)
    rw [hfront] at hx
    obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := hx
    have hzb : z ∈ C.curve 0 '' Icc (0 : ℝ) 1 := by
      have hh : C.curve 0 '' Icc (0 : ℝ) 1 = frontier (jordanInterior H) := by
        simpa only [C.disk_zero] using hpar.boundary
      rw [hh]
      exact hz
    obtain ⟨a, _ha, hca⟩ := hzb
    refine ⟨a, ?_⟩
    change F (π (C.curve 0 a : Sphere)) = 1
    rw [hca, hF (frontier_subset_closure (hf z hz)), he,
      centeredJordanCoordinate_boundary J hb, standardCirclePoint_zero]
  obtain ⟨a, reverse, q, hq, hq0, hq1, hqm, hqb⟩ := exists_ordered_unit_circuit
    (fun t => P (C.curve 0 t : Sphere))
    (P.continuous.comp (OnePoint.continuous_coe.comp hpar.smooth.continuous))
    hnorm (hpar.periodic.comp (fun z : ℂ => P (z : Sphere))) hi hstart
  obtain ⟨δ, hδ, hδw, hw, hw0, hw1⟩ := exists_punctured_physical_collar C P hn hb0
  exact exists_ordered_collar_lift_of_parameter C P a reverse q hq hq0 hq1 hqm hqb
    δ hδ hδw hw hw0 hw1

 theorem OrderedCollarLift.quotient_boundary_identification
    {π : Sphere → Sphere} (hπ : Continuous π)
    {H J : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J))) (θ : UnitAddCircle) :
    π (D.circuit 0 (D.angle.symm (unitCircleCut θ)) : Sphere) = centeredJordanBoundary J b θ := by
  let t := D.angle.symm (unitCircleCut θ)
  have ht := D.inverse_angle_mem θ
  have hz : π (D.circuit 0 t : Sphere) ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [hfront]
    refine ⟨_, ⟨D.circuit 0 t, ?_, rfl⟩, rfl⟩
    simpa only [C.disk_zero] using D.circuit_mem_frontier ⟨le_rfl, C.width_pos.le⟩ t
  apply centeredJordanCoordinate_injOn J hb (frontier_subset_closure hz)
    (frontier_subset_closure (centeredJordanBoundary_mem_frontier J hb θ))
  rw [← hF (frontier_subset_closure hz), centeredJordanCoordinate_boundary J hb]
  have hp := D.projects (0, t) ⟨⟨by linarith [D.width_pos], D.width_pos⟩, mem_univ _⟩
  rw [D.boundary t ht] at hp
  simp only [abs_zero] at hp
  change diskRayProjection (D.angle t : ℂ) = F (π (D.circuit 0 t : Sphere)) at hp
  rw [← hp]
  simp only [diskRayProjection, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.ofReal_one,
    Complex.ofReal_re, one_mul, t, D.angle.apply_symm_apply, unitCircleCut, AddCircle.coe_equivIco]

end CircleDomainRigidity

end

end OAI
