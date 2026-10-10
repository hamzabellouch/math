import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndGradientL2
import OAI.Analysis.Conductivity.Sobolev.CutSlopeH1

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma differentiable_cut_positive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ τ : X → ℝ} {x : X} (hχ : DifferentiableAt ℝ χ x)
    (hτ : DifferentiableAt ℝ τ x) (hne : τ x≠0) (κ : ℝ) :
    DifferentiableAt ℝ (fun x => κ*(χ x*max 0 (τ x))) x := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hτ.continuousAt.eventually (gt_mem_nhds hn)] with y hy
      simp [max_eq_left hy.le]
    exact (differentiableAt_const (0:ℝ)).congr_of_eventuallyEq he
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun x => κ*(χ x*τ x)) := by
      filter_upwards [hτ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
      rw [max_eq_right hy.le]
    exact ((hχ.mul hτ).const_mul κ).congr_of_eventuallyEq he

lemma fderiv_cut_positive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ τ : X → ℝ} {x : X} (hχ : DifferentiableAt ℝ χ x)
    (hτ : DifferentiableAt ℝ τ x) (hne : τ x≠0) (κ : ℝ) (v : X) :
    fderiv ℝ (fun x => κ*(χ x*max 0 (τ x))) x v=
      κ*(fderiv ℝ χ x v*max 0 (τ x)+χ x*(if 0<τ x then fderiv ℝ τ x v else 0)) := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hτ.continuousAt.eventually (gt_mem_nhds hn)] with y hy
      simp [max_eq_left hy.le]
    rw [he.fderiv_eq,fderiv_const_apply]
    simp [max_eq_left hn.le,not_lt_of_ge hn.le]
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun x => κ*(χ x*τ x)) := by
      filter_upwards [hτ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
      rw [max_eq_right hy.le]
    have hh := ((hχ.hasFDerivAt.mul hτ.hasFDerivAt).const_mul κ).fderiv
    simp only [Pi.mul_apply] at hh
    rw [he.fderiv_eq,hh]
    simp [smul_apply,add_apply,smul_eq_mul,max_eq_right hp.le,hp]
    ring

theorem compact_collar_slope_value_gradient {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a : ℝ} (ha : a≠0) {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (κ l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))) ∧
      ∀ i,weakGradient w x i=κ*(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))+
        χ (WithLp.ofLp x)*(if 0<a*(sourceCollarTime (WithLp.ofLp x)-b) then
          fderiv ℝ (fun y => a*(sourceCollarTime y-b)) (WithLp.ofLp x) (Pi.single i 1) else 0))) := by
  obtain ⟨w,hw,hwe⟩ := compact_collar_slope_H1 hχ hc hχb a b κ l r hl hr hχs
  refine ⟨w,hw,?_⟩
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hd := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (hK.ae_differentiableAt (μ:=volume)))
  have hn := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (sourceColevel_ae_ne hb))
  filter_upwards [hwe,hd,hn] with x hx hd hn
  refine ⟨hx.1,fun i => ?_⟩
  have hne : a*(sourceCollarTime (WithLp.ofLp x)-b)≠0 := mul_ne_zero ha (sub_ne_zero.mpr hn)
  have hχd := hχ.differentiable (by simp) (WithLp.ofLp x)
  have hD := differentiable_cut_positive hχd hd hne κ
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hE := hD.hasFDerivAt.comp x E.hasFDerivAt
  simp only [Function.comp_def] at hE
  rw [hx.2 i,hE.differentiableAt.lineDeriv_eq_fderiv,hE.fderiv,ContinuousLinearMap.comp_apply]
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  rw [hi]
  exact fderiv_cut_positive hχd hd hne κ _

end ScalarConductivity

end

end OAI
