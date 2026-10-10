import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse
import OAI.Analysis.BiholderTransport.Regularity.ReverseRegular

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_cost_branch_with_action (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (z.1,riemannianExp z.1 z.2) ∧
      (∀ᶠ r in 𝓝 z,G (r.1,riemannianExp r.1 r.2)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨P,hP,hPz,hleft,hright⟩ := exists_smooth_exp_branch z hz
  let G : M×M → ℝ := fun q => ‖(P q).2‖^2/2
  refine ⟨G,(contMDiff_tangent_energy (P (z.1,riemannianExp z.1 z.2))).comp _ hP,?_,?_⟩
  · filter_upwards [hleft] with r hr
    change ‖(P (r.1,riemannianExp r.1 r.2)).2‖^2/2=‖r.2‖^2/2
    rw [hr]
  let F : TangentBundle 𝓘(ℝ,Model n) M → M×M := fun r => (r.1,riemannianExp r.1 r.2)
  have hF : Continuous F :=
    ((Bundle.contMDiff_proj (fun v : M => TangentSpace 𝓘(ℝ,Model n) v)).prodMk contMDiff_riemannianExp).continuous
  have hPnear : ∀ᶠ q in 𝓝 (F z), ContinuousAt P q := by
    have hzero : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 0 P (F z) := hP.of_le bot_le
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hzero).mono
      (fun point hpoint => hpoint.continuousAt)
  have hRnear : ∀ᶠ q in 𝓝 (F z), ∀ᶠ q' in 𝓝 q,
      (P q').1=q'.1 ∧ riemannianExp (P q').1 (P q').2=q'.2 :=
    eventually_eventually_nhds.mpr hright
  filter_upwards [hleft,(hF.continuousAt.eventually (hPnear.and hRnear))] with r hr hnear
  intro hrID
  have hC : {v : TangentBundle 𝓘(ℝ,Model n) M | v.2 ∈ minimizingVectors v.1} ∈ 𝓝 (P (F r)) := by
    rw [show P (F r)=r from hr]
    exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors r hrID)
  have hmin := hnear.1.preimage_mem_nhds hC
  filter_upwards [hmin,hnear.2] with q hqmin hq
  change dist q.1 q.2^2/2=‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  have hd : dist q.1 q.2=‖(P q).2‖ :=
    (congrArg₂ dist hq.1.symm hq.2.symm).trans hqmin
  rw [hd]
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma contMDiff_reverseRay : ContMDiff
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (reverseRay (n := n) (M := M)) := by
  exact contMDiff_tangentScale.comp
    (contMDiff_const.prodMk (contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)))

lemma reverseRay_base (z : TangentBundle 𝓘(ℝ,Model n) M) :
    (reverseRay z).1=riemannianExp z.1 z.2 := by
  rw [riemannianExp_eq_sprayFlow]
  rfl

lemma reverseRay_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) :
    riemannianExp (reverseRay z).1 (reverseRay z).2=z.1 := by
  rw [←reverseRay_base,reverseRay_involutive]

lemma fiber_nonconjugate_of_smooth_left_inverse
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (P : M×M → TangentBundle 𝓘(ℝ,Model n) M)
    (hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,riemannianExp z.1 z.2))
    (hPz : P (z.1,riemannianExp z.1 z.2)=z)
    (hleft : ∀ᶠ r in 𝓝 z,P (r.1,riemannianExp r.1 r.2)=r) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z.1
  let y := riemannianExp z.1 z.2
  let d := extChartAt 𝓘(ℝ,Model n) y
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : V ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  let f : V → Model n := fun v => d (riemannianExp z.1 v)
  let g : Model n → Model n := fun w => (χ (P (z.1,d.symm w))).2
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d y) :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))
  have hp : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun w => P (z.1,d.symm w)) (d y) := by
    have hm : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
        (fun w => (z.1,d.symm w)) (d y) := contMDiffAt_const.prodMk hd
    have hP' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,d.symm (d y)) := by
      rw [hdy]; exact hP
    exact hP'.comp (d y) hm
  have hχ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n×Model n) ∞ χ (P (z.1,d.symm (d y))) := by
    rw [hdy,hPz]
    exact contMDiffAt_extChartAt
  have hg : ContDiffAt ℝ ∞ g (f z.2) :=
    contDiffAt_snd.comp (f z.2) (hχ.comp (d y) hp).contDiffAt
  have hf : ContDiffAt ℝ ∞ f z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hfiber : Continuous (fun v : V => (⟨z.1,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    (contMDiff_fiber_embedding z.1).continuous
  have hfleft : ∀ᶠ v in 𝓝 z.2,P (z.1,riemannianExp z.1 v)=⟨z.1,v⟩ :=
    hfiber.continuousAt.eventually hleft
  have hsrc : ∀ᶠ v in 𝓝 z.2,riemannianExp z.1 v∈d.source :=
    (continuous_riemannianExp z.1).continuousAt.eventually (extChartAt_source_mem_nhds y)
  have heq : g ∘ f =ᶠ[𝓝 z.2] L := by
    filter_upwards [hfleft,hsrc] with v hv hvs
    change (χ (P (z.1,d.symm (d (riemannianExp z.1 v))))).2=L v
    rw [d.left_inv hvs,hv]
    rfl
  have hD : (fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)=(L : V →L[ℝ] Model n) := by
    rw [←fderiv_comp _ (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp)),
      heq.fderiv_eq,L.fderiv]
  intro u v huv
  apply L.injective
  have H := congrArg (fderiv ℝ g (f z.2)) huv
  change ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) u=
    ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) v at H
  rw [hD] at H
  exact H

lemma reverseRay_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp (reverseRay z).1 (reverseRay z).2)
      (riemannianExp (reverseRay z).1 v)) (reverseRay z).2) := by
  obtain ⟨P,hP,hPz,hleft,_⟩ := exists_smooth_exp_branch z hz
  let Q : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => reverseRay (P (q.2,q.1))
  have hQ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Q
      ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) := by
    rw [reverseRay_endpoint,reverseRay_base]
    have hs : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := contMDiffAt_snd.prodMk contMDiffAt_fst
    have hp : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => P (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := hP.comp (riemannianExp z.1 z.2,z.1) hs
    exact contMDiff_reverseRay.contMDiffAt.comp (riemannianExp z.1 z.2,z.1) hp
  apply fiber_nonconjugate_of_smooth_left_inverse (reverseRay z) Q hQ
  · dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base,hPz]
  · have H := continuous_reverseRay.continuousAt.eventually
      (show ∀ᶠ r in 𝓝 (reverseRay (reverseRay z)),P (r.1,riemannianExp r.1 r.2)=r from
        by rw [reverseRay_involutive]; exact hleft)
    filter_upwards [H] with r hr
    dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base] at hr
    rw [hr,reverseRay_involutive]

end WeakMTWTransport

end

end OAI
