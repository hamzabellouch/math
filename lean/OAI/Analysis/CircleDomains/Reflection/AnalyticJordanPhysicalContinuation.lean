import OAI.Analysis.CircleDomains.Reflection.ConformalChartTransport
import OAI.Analysis.CircleDomains.Reflection.RoundExteriorChartSides

namespace OAI

/-! The continuation of a circularization map on an open neighborhood
in the original source plane, with the chart inverse constructed. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma analytic_jordan_physical_continuation_sides {S : Set ℂ} {α : ℂ → ℂ}
    {c d p : ℂ} {r s : ℝ} {f : Sphere → Sphere}
    (hS : IsOpen S) (hα : DifferentiableOn ℂ α S) (hi : InjOn α S)
    (hr : 0<r) (hs : 0<s) (hp : ‖p‖=1) (hDS : closedBall c r⊆S)
    (hf : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃ (W : Set ℂ) (G : ℂ → ℂ), IsOpen W ∧ α (c+(r:ℂ)*p)∈W ∧
      DifferentiableOn ℂ G W ∧ InjOn G W ∧
      EqOn G (fun z => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere))))
        (W∩(α '' closedBall c r)ᶜ) ∧ (∀z∈W,deriv G z≠0) ∧ ∀z∈W,‖G z‖<1 ↔ z∉α '' closedBall c r := by
  let κ := roundExteriorBoundaryChart c r p
  let ψ := α ∘ κ
  have hκd : DifferentiableOn ℂ κ (ball 0 1) := by
    intro z hz
    exact (roundExteriorBoundaryChart_differentiable c p r
      (mem_ball_zero_iff.mp hz)).differentiableWithinAt
  have hp0 : p≠0 := norm_ne_zero_iff.mp (by rw [hp];norm_num)
  let N := ball (0:ℂ) 1 ∩ κ ⁻¹' S
  have hN : IsOpen N := hκd.continuousOn.isOpen_inter_preimage isOpen_ball hS
  have hκ0 : κ 0=c+(r:ℂ)*p := by
    simp only [κ,roundExteriorBoundaryChart,unitExteriorBoundaryChart_zero]
  have h0D : κ 0∈closedBall c r := by
    rw [hκ0,mem_closedBall_iff_norm,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hp,mul_one]
  have h0N : (0:ℂ)∈N := ⟨mem_ball_self zero_lt_one,hDS h0D⟩
  have hψd : DifferentiableOn ℂ ψ N :=
    hα.comp (hκd.mono inter_subset_left) (fun _ hz => hz.2)
  have hψi : InjOn ψ N := hi.comp
    ((roundExteriorBoundaryChart_injOn c hr hp0).mono inter_subset_left) (fun _ hz => hz.2)
  obtain ⟨V,F,hV,h0V,hFd,hFi,hFe,_,hFs⟩ :=
    analytic_jordan_boundary_injective_continuation_sides hS hα hi hr hs hp hDS hf
  obtain ⟨W,G,hW,h0,hWeq,hGd,hGi,hGe⟩ :=
    transport_injective_holomorphic_chart hN hV h0N h0V hψd hψi hFd hFi
  have h0' : α (c+(r:ℂ)*p)∈W := by
    change α (κ 0)∈W at h0
    rwa [hκ0] at h0
  refine ⟨W,G,hW,h0',hGd,hGi,?_,fun z hz => holomorphicInjOn_deriv_ne_zero hW hGd hGi hz,?_⟩
  · intro x hx
    rw [hWeq] at hx
    obtain ⟨z,hz,rfl⟩ := hx.1
    have hzpos : 0<z.im := by
      by_contra hn
      apply hx.2
      exact ⟨κ z,roundExteriorBoundaryChart_mem_closedBall hr hp
        (mem_ball_zero_iff.mp hz.1.1) (le_of_not_gt hn),rfl⟩
    rw [hGe z hz]
    exact hFe ⟨hz.2,hzpos⟩
  · intro x hx
    rw [hWeq] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    rw [hGe z hz,hFs z hz.2]
    change 0<z.im ↔ α (κ z)∉α '' closedBall c r
    rw [←roundExteriorBoundaryChart_outside_iff hr hp (mem_ball_zero_iff.mp hz.1.1)]
    constructor
    · intro hout himage
      obtain ⟨w,hw,he⟩ := himage
      have hwz : w=κ z := hi (hDS hw) hz.1.2 he
      exact hout (hwz ▸ hw)
    · intro hout hzin
      exact hout ⟨κ z,hzin,rfl⟩

lemma analytic_jordan_physical_continuation {S : Set ℂ} {α : ℂ → ℂ}
    {c d p : ℂ} {r s : ℝ} {f : Sphere → Sphere}
    (hS : IsOpen S) (hα : DifferentiableOn ℂ α S) (hi : InjOn α S)
    (hr : 0<r) (hs : 0<s) (hp : ‖p‖=1) (hDS : closedBall c r⊆S)
    (hf : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃ (W : Set ℂ) (G : ℂ → ℂ), IsOpen W ∧ α (c+(r:ℂ)*p)∈W ∧
      DifferentiableOn ℂ G W ∧ InjOn G W ∧
      EqOn G (fun z => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere))))
        (W∩(α '' closedBall c r)ᶜ) ∧ ∀z∈W,deriv G z≠0 := by
  obtain ⟨W,G,hW,hp,hGd,hGi,hGe,hGn,_⟩ :=
    analytic_jordan_physical_continuation_sides hS hα hi hr hs hp hDS hf
  exact ⟨W,G,hW,hp,hGd,hGi,hGe,hGn⟩

end CircleDomainRigidity

end

end OAI
