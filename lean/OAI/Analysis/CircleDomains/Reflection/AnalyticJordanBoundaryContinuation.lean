import OAI.Analysis.CircleDomains.Reflection.RoundExteriorBoundaryInjectivity
import OAI.Analysis.CircleDomains.Reflection.InjectiveConformalBoundaryChart

namespace OAI

/-! Continuation at a Jordan boundary which is the injective holomorphic
image of a round circle. This is the boundary geometry retained after a
hole has been circularized and then transported by later stages. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma analytic_jordan_boundary_injective_continuation_sides {S : Set ℂ} {α : ℂ → ℂ}
    {c d p : ℂ} {r s : ℝ} {f : Sphere → Sphere}
    (hS : IsOpen S) (hα : DifferentiableOn ℂ α S) (hi : InjOn α S)
    (hr : 0<r) (hs : 0<s) (hp : ‖p‖=1) (hDS : closedBall c r⊆S)
    (hf : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization d s hs
        (f (α (roundExteriorBoundaryChart c r p z) : Sphere))))
        (V∩{z : ℂ | 0<z.im}) ∧ (∀z∈V,deriv F z≠0) ∧ ∀z∈V,‖F z‖<1 ↔ 0<z.im := by
  let κ := roundExteriorBoundaryChart c r p
  have hκ0 : κ 0=c+(r:ℂ)*p := by
    simp only [κ,roundExteriorBoundaryChart,unitExteriorBoundaryChart_zero]
  have h0D : κ 0∈closedBall c r := by
    rw [hκ0,mem_closedBall_iff_norm,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hp,mul_one]
  have hκc : ContinuousAt κ 0 :=
    (roundExteriorBoundaryChart_differentiable c p r (by simp)).continuousAt
  obtain ⟨δ,hδ,hδS⟩ := Metric.mem_nhds_iff.mp (hκc.eventually (hS.mem_nhds (hDS h0D)))
  let R := min (1/2:ℝ) (δ/2)
  have hR : 0<R := by dsimp [R];positivity
  have hR1 : R<1 := by dsimp [R];nlinarith [min_le_left (1/2:ℝ) (δ/2)]
  have hRδ : R<δ := by dsimp [R];nlinarith [min_le_right (1/2:ℝ) (δ/2)]
  have hκS : ∀z:ℂ,‖z‖≤R → κ z∈S := by
    intro z hz
    exact hδS (by simpa only [mem_ball_zero_iff] using hz.trans_lt hRδ)
  let E := α '' closedBall c r
  let U := (((↑) : ℂ → Sphere) '' E)ᶜ
  have hEc : IsCompact E := (isCompact_closedBall c r).image_of_continuousOn
    (hα.continuousOn.mono hDS)
  have hU : IsOpen U := (hEc.image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hkdiff (z : ℂ) (hz : ‖z‖≤R) : DifferentiableAt ℂ κ z :=
    roundExteriorBoundaryChart_differentiable c p r (hz.trans_lt hR1)
  have hdiff : DifferentiableOn ℂ (α ∘ κ) (upperSemidisk R) := by
    intro z hz
    have hzR := (mem_ball_zero_iff.mp hz.1).le
    exact (((hα _ (hκS z hzR)).differentiableAt (hS.mem_nhds (hκS z hzR))).comp z
      (hkdiff z hzR)).differentiableWithinAt
  have hm : ∀z∈upperSemidisk R,((α ∘ κ) z : Sphere)∈U := by
    intro z hz
    rintro ⟨w,⟨v,hv,he⟩,hwe⟩
    have hae : α v=α (κ z) := he.trans (OnePoint.coe_injective hwe)
    have hvz : v=κ z := hi (hDS hv) (hκS z (mem_ball_zero_iff.mp hz.1).le) hae
    apply roundExteriorBoundaryChart_exterior hr hp
      ((mem_ball_zero_iff.mp hz.1).trans hR1) hz.2
    exact hvz ▸ hv
  have hc : ∀z:ℂ,‖z‖≤R → z.im=0 → ContinuousAt (α ∘ κ) z := by
    intro z hz _
    exact ((hα _ (hκS z hz)).differentiableAt (hS.mem_nhds (hκS z hz))).continuousAt.comp
      (hkdiff z hz).continuousAt
  have hb : ∀z:ℂ,‖z‖≤R → z.im=0 → ((α ∘ κ) z : Sphere)∉U := by
    intro z _ hz hnot
    apply hnot
    refine ⟨α (κ z),⟨κ z,?_,rfl⟩,rfl⟩
    exact sphere_subset_closedBall (roundExteriorBoundaryChart_boundary hr hp hz)
  have hp0 : p≠0 := norm_ne_zero_iff.mp (by rw [hp];norm_num)
  have hkI : InjOn (α ∘ κ) (upperSemidisk R) := by
    apply hi.comp
    · exact (roundExteriorBoundaryChart_injOn c hr hp0).mono
        (fun z hz => mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz.1).trans hR1))
    · exact fun z hz => hκS z (mem_ball_zero_iff.mp hz.1).le
  obtain ⟨V,F,hV,h0,_,hFd,hFi,hFe,hFn,hFs⟩ := injective_circular_exterior_boundary_chart_sides hU hf hs hR
    hdiff hkI hm hc hb
  exact ⟨V,F,hV,h0,hFd,hFi,hFe,hFn,hFs⟩

lemma analytic_jordan_boundary_injective_continuation {S : Set ℂ} {α : ℂ → ℂ}
    {c d p : ℂ} {r s : ℝ} {f : Sphere → Sphere}
    (hS : IsOpen S) (hα : DifferentiableOn ℂ α S) (hi : InjOn α S)
    (hr : 0<r) (hs : 0<s) (hp : ‖p‖=1) (hDS : closedBall c r⊆S)
    (hf : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
      DifferentiableOn ℂ F V ∧ InjOn F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization d s hs
        (f (α (roundExteriorBoundaryChart c r p z) : Sphere))))
        (V∩{z : ℂ | 0<z.im}) ∧ ∀z∈V,deriv F z≠0 := by
  obtain ⟨V,F,hV,h0,hFd,hFi,hFe,hFn,_⟩ :=
    analytic_jordan_boundary_injective_continuation_sides hS hα hi hr hs hp hDS hf
  exact ⟨V,F,hV,h0,hFd,hFi,hFe,hFn⟩

lemma analytic_jordan_boundary_continuation {S : Set ℂ} {α : ℂ → ℂ}
    {c d p : ℂ} {r s : ℝ} {f : Sphere → Sphere}
    (hS : IsOpen S) (hα : DifferentiableOn ℂ α S) (hi : InjOn α S)
    (hr : 0<r) (hs : 0<s) (hp : ‖p‖=1) (hDS : closedBall c r⊆S)
    (hf : IsConformalEquivalence f
      ((((↑) : ℂ → Sphere) '' (α '' closedBall c r))ᶜ)
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧
      DifferentiableOn ℂ F V ∧
      EqOn F (fun z => finiteCoord (exteriorDiskNormalization d s hs
        (f (α (roundExteriorBoundaryChart c r p z) : Sphere))))
        (V∩{z : ℂ | 0<z.im}) := by
  obtain ⟨V,F,hV,h0,hFd,_,hFe,_⟩ :=
    analytic_jordan_boundary_injective_continuation hS hα hi hr hs hp hDS hf
  exact ⟨V,F,hV,h0,hFd,hFe⟩

end CircleDomainRigidity

end

end OAI
