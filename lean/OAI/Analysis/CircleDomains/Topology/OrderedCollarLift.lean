import OAI.Analysis.CircleDomains.Topology.OrderedPhysicalCollar

namespace OAI

/-! A jointly lifted physical collar, normalized at the boundary. All
fields below are constructed from the regular collar and its actual disk
coordinate; in particular, positive winding is not an input assumption. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure OrderedCollarLift {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (F : C(Sphere, ℂ)) where
  start : ℝ
  reverse : Bool
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ C.width
  angle : ℝ ≃o ℝ
  angle_zero : angle 0 = 0
  angle_one : angle 1 = 1
  lift : ℝ × ℝ → ClosedUpperHalfPlane
  continuous : ContinuousOn lift (Ioo (-width) width ×ˢ univ)
  projects : ∀ p ∈ Ioo (-width) width ×ˢ (univ : Set ℝ),
    diskRayProjection (lift p).val =
      F (C.curve |p.1| (orientedParameter start reverse p.2) : Sphere)
  period : ∀ ρ ∈ Ioo (-width) width, lift (ρ, 1) = (lift (ρ, 0)).translate 1
  boundary : ∀ t ∈ Icc (0 : ℝ) 1, (lift (0, t)).val = (angle t : ℂ)
  approach : ∀ ε > 0, ∃ η > 0, η < width ∧ ∀ ρ ∈ Ioo (-η) η,
    ∀ t ∈ Icc (0 : ℝ) 1, dist (lift (ρ, t)).val (angle t : ℂ) < ε

 theorem exists_ordered_collar_lift_of_parameter
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) (F : C(Sphere, ℂ))
    (a : ℝ) (reverse : Bool) (q : ℝ → ℝ) (hq : Continuous q)
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) (hqm : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ t, F (C.curve 0 (orientedParameter a reverse t) : Sphere) =
      diskRayProjection (q t : ℂ))
    (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)
    (hw : ContinuousOn (fun p : ℝ × ℝ => F (C.curve |p.1| p.2 : Sphere))
      (Ioo (-δ) δ ×ˢ univ))
    (hw0 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), F (C.curve |p.1| p.2 : Sphere) ≠ 0)
    (hw1 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), ‖F (C.curve |p.1| p.2 : Sphere)‖ ≤ 1) :
    Nonempty (OrderedCollarLift C F) := by
  obtain ⟨e, he0, he1, heq⟩ := exists_boundary_orderIso q hq hqm hq0 hq1
  let w : ℝ × ℝ → ℂ := fun p => F (C.curve |p.1| (orientedParameter a reverse p.2) : Sphere)
  have hc : ContinuousOn w (Ioo (-δ) δ ×ˢ univ) := by
    apply hw.comp (continuous_fst.prodMk
      ((contDiff_orientedParameter a reverse).continuous.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  have hzero (p : ℝ × ℝ) (hp : p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ)) : w p ≠ 0 :=
    hw0 (p.1, orientedParameter a reverse p.2) ⟨hp.1, mem_univ _⟩
  have hnorm (p : ℝ × ℝ) (hp : p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ)) : ‖w p‖ ≤ 1 :=
    hw1 (p.1, orientedParameter a reverse p.2) ⟨hp.1, mem_univ _⟩
  have hboundary (t : ℝ) : w (0, t) = diskRayProjection (q t : ℂ) := by
    simpa only [w, abs_zero] using hqb t
  obtain ⟨L, hL, hp, hB⟩ := exists_boundary_normalized_logarithmic_lift hδ w hc hzero hnorm
    q hq hq0 hboundary
  have hloop (ρ : ℝ) (hρ : ρ ∈ Ioo (-δ) δ) : w (ρ, 1) = w (ρ, 0) := by
    have habs : |ρ| ∈ Icc 0 C.width := ⟨abs_nonneg _, (abs_lt.mpr hρ).le.trans hδw⟩
    exact congrArg (fun z : ℂ => F (z : Sphere))
      (orientedCircuit_periodic (C.parametrization |ρ| habs).periodic a reverse).eq
  have hperiod := boundary_normalized_collar_lift_period hδ w L hL hp hloop q
    (by rw [hq0, hq1]; norm_num) hB
  refine ⟨{
    start := a, reverse := reverse, width := δ, width_pos := hδ, width_le := hδw,
    angle := e, angle_zero := he0, angle_one := he1,
    lift := L, continuous := hL, projects := hp, period := hperiod,
    boundary := ?_, approach := ?_ }⟩
  · intro t ht
    rw [hB t, heq ht]
  · intro ε hε
    obtain ⟨η, hη, hηδ, hnear⟩ := uniform_collar_lift_approach hδ L hL q hB ε hε
    refine ⟨η, hη, hηδ, ?_⟩
    intro ρ hρ t ht
    rw [heq ht]
    exact hnear ρ hρ t ht

 theorem exists_ordered_collar_lift
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {b : ℂ} (hb : b ∈ jordanInterior H)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate H (b : Sphere))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    Nonempty (OrderedCollarLift C F) := by
  obtain ⟨a, reverse, q, hq, hq0, hq1, hqm, hqb⟩ := exists_ordered_physical_collar C hb F hF
  obtain ⟨δ, hδ, hδw, hw, hw0, hw1, _⟩ := exists_centered_punctured_collar_family C hb F hF
  exact exists_ordered_collar_lift_of_parameter C F a reverse q hq hq0 hq1 hqm hqb
    δ hδ hδw hw hw0 hw1

namespace OrderedCollarLift

 def circuit {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) (ρ : ℝ) : ℝ → ℂ :=
  C.curve ρ ∘ orientedParameter D.start D.reverse

 theorem circuit_smooth {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) :
    ContDiff ℝ (⊤ : ℕ∞) (D.circuit ρ) :=
  (C.parametrization ρ hρ).smooth.comp (contDiff_orientedParameter D.start D.reverse)

 theorem circuit_periodic {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) :
    Function.Periodic (D.circuit ρ) 1 :=
  orientedCircuit_periodic (C.parametrization ρ hρ).periodic D.start D.reverse

 theorem circuit_mem_frontier {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) (t : ℝ) :
    D.circuit ρ t ∈ frontier (jordanInterior (C.disk ρ)) :=
  (C.parametrization ρ hρ).mem_frontier _

 theorem abs_circleFormIntegral {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width)
    (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) :
    |circleFormIntegral φ u (D.circuit ρ)| = |circleFormIntegral φ u (C.curve ρ)| :=
  abs_circleFormIntegral_oriented φ u ((C.parametrization ρ hρ).smooth.differentiable (by simp))
    (C.parametrization ρ hρ).periodic D.start D.reverse

 theorem continuous_slice {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Ioo (-D.width) D.width) :
    Continuous (fun t : ℝ => D.lift (ρ, t)) :=
  D.continuous.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hρ, mem_univ _⟩)

 theorem inverse_angle_mem {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) (θ : UnitAddCircle) :
    D.angle.symm (unitCircleCut θ) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply D.angle.le_iff_le.mp
    simpa only [D.angle_zero, D.angle.apply_symm_apply] using (unitCircleCut_mem θ).1
  · apply D.angle.le_iff_le.mp
    simpa only [D.angle_one, D.angle.apply_symm_apply] using (unitCircleCut_mem θ).2.le

 theorem boundary_identification {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {b : ℂ} (hb : b ∈ jordanInterior H)
    (hF : EqOn F (centeredJordanCoordinate H (b : Sphere))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior H))) (θ : UnitAddCircle) :
    (D.circuit 0 (D.angle.symm (unitCircleCut θ)) : Sphere) = centeredJordanBoundary H (b : Sphere) θ := by
  let t := D.angle.symm (unitCircleCut θ)
  have ht : t ∈ Icc (0 : ℝ) 1 := D.inverse_angle_mem θ
  have hbs : (b : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H := ⟨b, hb, rfl⟩
  have hz : (D.circuit 0 t : Sphere) ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [frontier_sphere_image_jordanInterior]
    refine ⟨_, ?_, rfl⟩
    simpa only [C.disk_zero] using D.circuit_mem_frontier ⟨le_rfl, C.width_pos.le⟩ t
  apply centeredJordanCoordinate_injOn H hbs (frontier_subset_closure hz)
    (frontier_subset_closure (centeredJordanBoundary_mem_frontier H hbs θ))
  rw [← hF (frontier_subset_closure hz), centeredJordanCoordinate_boundary H hbs]
  have hp := D.projects (0, t) ⟨⟨by linarith [D.width_pos], D.width_pos⟩, mem_univ _⟩
  rw [D.boundary t ht] at hp
  rw [show |(0 : ℝ)| = 0 from abs_zero] at hp
  change diskRayProjection (D.angle t : ℂ) = F (D.circuit 0 t : Sphere) at hp
  change F (D.circuit 0 t : Sphere) = standardCirclePoint θ
  rw [← hp]
  simp only [diskRayProjection, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.ofReal_one,
    Complex.ofReal_re, one_mul, t, D.angle.apply_symm_apply, unitCircleCut, AddCircle.coe_equivIco]

end OrderedCollarLift
end CircleDomainRigidity

end

end OAI
