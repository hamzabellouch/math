import OAI.Analysis.CircleDomains.Topology.CircleArgumentOrder
import OAI.Analysis.CircleDomains.Selection.CircuitReparametrization
import OAI.Analysis.CircleDomains.Topology.CenteredBoundary

namespace OAI

/-! The actual centered Jordan boundary admits a smooth physical circuit
whose disk angle is increasing from zero to one. Only the starting point
and direction of the original regular circuit are changed. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def orientedParameter (a : ℝ) (reverse : Bool) (t : ℝ) : ℝ :=
  if reverse then a + (1 - t) else a + t

 theorem contDiff_orientedParameter (a : ℝ) (reverse : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (orientedParameter a reverse) := by
  cases reverse
  · exact contDiff_const.add contDiff_id
  · exact contDiff_const.add (contDiff_const.sub contDiff_id)

 theorem orientedCircuit_periodic {α : Type*} {γ : ℝ → α}
    (hp : Function.Periodic γ 1) (a : ℝ) (reverse : Bool) :
    Function.Periodic (γ ∘ orientedParameter a reverse) 1 := by
  cases reverse
  · exact periodic_shift hp a
  · exact periodic_reverse (periodic_shift hp a)

 theorem abs_circleFormIntegral_oriented
    (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) {γ : ℝ → ℂ}
    (hγ : Differentiable ℝ γ) (hp : Function.Periodic γ 1) (a : ℝ) (reverse : Bool) :
    |circleFormIntegral φ u (γ ∘ orientedParameter a reverse)| = |circleFormIntegral φ u γ| := by
  cases reverse
  · exact congrArg abs (circleFormIntegral_shift φ u hp a)
  · change |circleFormIntegral φ u (fun t => (fun s => γ (a + s)) (1 - t))| = _
    have hd : Differentiable ℝ (fun s : ℝ => γ (a + s)) := by
      apply hγ.comp
      exact (contDiff_const.add contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => a + s)).differentiable (by simp)
    rw [circleFormIntegral_reverse φ u hd, abs_neg, circleFormIntegral_shift φ u hp a]

 theorem exists_ordered_unit_circuit
    (γ : ℝ → ℂ) (hc : Continuous γ) (hn : ∀ t, ‖γ t‖ = 1)
    (hper : Function.Periodic γ 1) (hi : InjOn γ (Ico (0 : ℝ) 1))
    (hstart : ∃ a, γ a = 1) :
    ∃ (a : ℝ) (reverse : Bool) (q : ℝ → ℝ), Continuous q ∧ q 0 = 0 ∧ q 1 = 1 ∧
      StrictMonoOn q (Icc (0 : ℝ) 1) ∧
      ∀ t, γ (orientedParameter a reverse t) = diskRayProjection (q t : ℂ) := by
  obtain ⟨a, ha⟩ := hstart
  let z : ℝ → ℂ := fun t => γ (a + t)
  have hz : Continuous z := hc.comp (continuous_const.add continuous_id)
  have hz0 : z 0 = 1 := by simpa only [z, add_zero] using ha
  obtain ⟨q, hq, hq0, hproj, hord⟩ := exists_ordered_argument_lift z hz
    (fun t => hn (a + t)) (periodic_shift hper a) (periodic_shift_injOn hper hi a)
  have hp (t : ℝ) : z t = diskRayProjection (q t : ℂ) := by
    apply normalizedArgument_injective_on_unit_sphere (hn (a + t))
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, Complex.ofReal_re, hproj t, hz0, div_one]
  rcases hord with ⟨hm, hq1⟩ | ⟨hm, hq1⟩
  · exact ⟨a, false, q, hq, hq0, hq1, hm, hp⟩
  · let r : ℝ → ℝ := fun t => q (1 - t) + 1
    have hr0 : r 0 = 0 := by simp only [r, sub_zero, hq1, neg_add_cancel]
    have hr1 : r 1 = 1 := by simp only [r, sub_self, hq0, zero_add]
    have hrm : StrictMonoOn r (Icc (0 : ℝ) 1) := by
      intro s hs t ht hst
      dsimp only [r]
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hh : q (1 - s) < q (1 - t) := hm ht' hs' (by linarith)
      exact add_lt_add_of_lt_of_le hh le_rfl
    refine ⟨a, true, r, (hq.comp (continuous_const.sub continuous_id)).add continuous_const,
      hr0, hr1, hrm, ?_⟩
    intro t
    change z (1 - t) = diskRayProjection (r t : ℂ)
    rw [hp]
    apply normalizedArgument_injective_on_unit_sphere
      (by rw [diskRayProjection_norm]; simp)
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, diskRayProjection_argument, Complex.ofReal_re, Complex.ofReal_re]
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 1 0).mpr ⟨1, by norm_num⟩
    simp only [r, AddCircle.coe_add, hone, add_zero]

 theorem exists_ordered_physical_collar
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {b : ℂ} (hb : b ∈ jordanInterior H)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate H (b : Sphere))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    ∃ (a : ℝ) (reverse : Bool) (q : ℝ → ℝ), Continuous q ∧ q 0 = 0 ∧ q 1 = 1 ∧
      StrictMonoOn q (Icc (0 : ℝ) 1) ∧
      ∀ t, F (C.curve 0 (orientedParameter a reverse t) : Sphere) =
        diskRayProjection (q t : ℂ) := by
  have hpar := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hbs : (b : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H := ⟨b, hb, rfl⟩
  have hbdy : C.curve 0 '' Icc (0 : ℝ) 1 = frontier (jordanInterior H) := by
    simpa only [C.disk_zero] using hpar.boundary
  have hfpoint := centeredJordanBoundary_mem_frontier H hbs (0 : UnitAddCircle)
  rw [frontier_sphere_image_jordanInterior] at hfpoint
  obtain ⟨x, hx, hxs⟩ := hfpoint
  obtain ⟨a, _ha, hca⟩ := (show x ∈ C.curve 0 '' Icc (0 : ℝ) 1 by rw [hbdy]; exact hx)
  have hfront (t : ℝ) : (C.curve 0 t : Sphere) ∈
      frontier (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [frontier_sphere_image_jordanInterior]
    refine ⟨_, ?_, rfl⟩
    simpa only [C.disk_zero] using hpar.mem_frontier t
  have ha1 : F (C.curve 0 a : Sphere) = 1 := by
    rw [hF (frontier_subset_closure (hfront a)), hca, hxs,
      centeredJordanCoordinate_boundary H hbs, standardCirclePoint_zero]
  let z : ℝ → ℂ := fun t => F (C.curve 0 (a + t) : Sphere)
  have hz : Continuous z := F.continuous.comp
    (OnePoint.continuous_coe.comp (hpar.smooth.continuous.comp (continuous_const.add continuous_id)))
  have hn (t : ℝ) : ‖z t‖ = 1 := by
    dsimp only [z]
    rw [hF (frontier_subset_closure (hfront _))]
    exact centeredJordanCoordinate_norm_boundary H hbs (hfront _)
  have hz0 : z 0 = 1 := by simpa only [z, add_zero] using ha1
  have hzi : InjOn z (Ico (0 : ℝ) 1) := by
    intro s hs t ht he
    apply periodic_shift_injOn hpar.periodic hpar.injective a hs ht
    apply OnePoint.coe_injective
    apply centeredJordanCoordinate_injOn H hbs
      (frontier_subset_closure (hfront _)) (frontier_subset_closure (hfront _))
    simpa only [z, hF (frontier_subset_closure (hfront _))] using he
  have hzp : Function.Periodic z 1 := (periodic_shift hpar.periodic a).comp
    (fun x : ℂ => F (x : Sphere))
  obtain ⟨q, hq, hq0, hproj, hord⟩ := exists_ordered_argument_lift z hz hn hzp hzi
  have hp (t : ℝ) : z t = diskRayProjection (q t : ℂ) := by
    apply normalizedArgument_injective_on_unit_sphere (hn t)
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, Complex.ofReal_re, hproj t, hz0, div_one]
  rcases hord with ⟨hm, hq1⟩ | ⟨hm, hq1⟩
  · exact ⟨a, false, q, hq, hq0, hq1, hm, hp⟩
  · let r : ℝ → ℝ := fun t => q (1 - t) + 1
    have hr0 : r 0 = 0 := by simp only [r, sub_zero, hq1, neg_add_cancel]
    have hr1 : r 1 = 1 := by simp only [r, sub_self, hq0, zero_add]
    have hrm : StrictMonoOn r (Icc (0 : ℝ) 1) := by
      intro s hs t ht hst
      dsimp only [r]
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hh : q (1 - s) < q (1 - t) := hm ht' hs' (by linarith)
      exact add_lt_add_of_lt_of_le hh le_rfl
    refine ⟨a, true, r, (hq.comp (continuous_const.sub continuous_id)).add continuous_const,
      hr0, hr1, hrm, ?_⟩
    intro t
    change z (1 - t) = diskRayProjection (r t : ℂ)
    rw [hp]
    apply normalizedArgument_injective_on_unit_sphere
      (by rw [diskRayProjection_norm]; simp)
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, diskRayProjection_argument, Complex.ofReal_re, Complex.ofReal_re]
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 1 0).mpr ⟨1, by norm_num⟩
    simp only [r, AddCircle.coe_add, hone, add_zero]

end CircleDomainRigidity

end

end OAI
