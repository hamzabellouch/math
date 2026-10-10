import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.NormLower
import OAI.Analysis.BiholderTransport.Volume.IntrinsicJacobian
import OAI.Analysis.BiholderTransport.Regularity.MixedIntrinsic

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section NormalTestChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance normalTestFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] in
lemma exists_chart_covector_for_log_fixed {a x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp : p∈injectivityDomain x) :
    let z := extChartAt 𝓘(ℝ,Model n) a x
    ∃ L : Model n →L[ℝ] ℝ,
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,L)=riemannianExp x p ∧
      HasFDerivAt (chartCost a (riemannianExp x p)) (-L) z := by
  let : Nonempty M := ⟨a⟩
  let z := extChartAt 𝓘(ℝ,Model n) a x
  let A : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,0⟩
  let P : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) A
  let L := riemannianCoordinateMetric a z (c P).2
  have hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source hx
  have hPs : P∈c.source := (tangent_chart_source_iff A P).mpr hx
  have he : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)=P := by
    rw [chartGradientVector_total_eq (q := (z,L)) hz]
    have hinv : (riemannianCoordinateMetric a z).inverse L=(c P).2 :=
      (riemannianCoordinateMetric_isInvertible hz).inverse_apply_self _
    rw [hinv]
    exact c.left_inv hPs
  have hreg : chartGradientVector a z L∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
    have H : P∈{Q : TangentBundle 𝓘(ℝ,Model n) M | Q.2∈injectivityDomain Q.1} := hp
    rwa [←he] at H
  have hex : coordinateBackward a (-1,z,L)=riemannianExp x p := by
    rw [coordinateBackward_eq_exp_chartGradient hz]
    exact congrArg (fun Q : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp Q.1 Q.2) he
  refine ⟨L,hreg,hex,?_⟩
  rw [←hex]
  exact chartCost_gradient_at_contact hz hreg

omit [Nonempty M] in
lemma normal_test_to_chart {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) (hp:p∈injectivityDomain x)
    {u:M → ℝ} {φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hφ:ContDiffAt ℝ 2 φ 0) (hφD:fderiv ℝ φ 0=innerSL ℝ p)
    (hval:u x=φ 0) (hlo:∀ᶠ w in 𝓝 0,φ w≤u (riemannianExp x w))
    (hpos:∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) :
    let z:=extChartAt 𝓘(ℝ,Model n) a x
    ∃ψ:Model n → ℝ,∃R:Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ 2 ψ z ∧
      chartGradientVector a z (fderiv ℝ ψ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,fderiv ℝ ψ z)=riemannianExp x p ∧
      u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z ∧
      (∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      (∃k>0,∀d:Model n,k*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d d) ∧
      chartJacobian (n:=n) a x*R.toLinearMap.normDet=1 ∧
      bilinearOperator (fderiv ℝ (fderiv ℝ ψ) z+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z)=
        R.adjoint.comp ((bilinearOperator
          (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).comp R) := by
  let z:=extChartAt 𝓘(ℝ,Model n) a x
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let c:=normalCost x p
  obtain ⟨m,hm,hpos⟩:=hpos
  obtain ⟨L,hLreg,hLb,hLD⟩:=exists_chart_covector_for_log_fixed hx hp
  obtain ⟨e,he,he0,hei,hi⟩:=exists_smooth_chart_fiber_log (a:=a)
    (zero_mem_injectivityDomain (n:=n) x) (by simpa only [riemannianExp_zero] using hx)
  simp only [riemannianExp_zero] at he he0 hei hi
  change ContDiffAt ℝ ∞ e z at he
  change e z=0 at he0
  change Function.Injective (fderiv ℝ e z) at hi
  have he2:ContDiffAt ℝ 2 e z:=he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨k,hk,Hk⟩:=exists_norm_sq_lower_of_injective (fderiv ℝ e z) hi
  let ψ:Model n → ℝ:=fun w=>φ (e w)
  let R:=fderiv ℝ e z
  have hψ:ContDiffAt ℝ 2 ψ z:=(he0.symm ▸ hφ).comp z he2
  have hc:ContDiffAt ℝ 2 c 0:=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hce:chartCost a (riemannianExp x p)=ᶠ[𝓝 z] (fun w=>c (e w)):=by
    filter_upwards [hei] with w hw
    simp only [c,normalCost,chartCost,hw]
  have hcc:ContDiffAt ℝ 2 (chartCost a (riemannianExp x p)) z:=
    ((he0.symm ▸ hc).comp z he2).congr_of_eventuallyEq hce
  have hψD:fderiv ℝ ψ z=L:=by
    have Hc:=hce.fderiv_eq (𝕜:=ℝ)
    rw [hLD.fderiv,fderiv_fun_comp z
      (by simpa only [he0] using hc.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,(normalCost_hasFDerivAt_zero hp).fderiv] at Hc
    rw [show ψ=(fun w=>φ (e w)) from rfl,fderiv_fun_comp z
      (by simpa only [he0] using hφ.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hφD]
    apply ContinuousLinearMap.ext
    intro d
    have HH:=congrArg (fun A:Model n →L[ℝ] ℝ=>A d) Hc
    simpa only [neg_apply,ContinuousLinearMap.comp_apply,
      innerSL_apply_apply,inner_neg_left,neg_inj] using HH.symm
  have hψlo:∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w):=by
    have HH:=he.continuousAt.eventually
      (show ∀ᶠ v in 𝓝 (e z),φ v≤u (riemannianExp x v) by rwa [he0])
    filter_upwards [HH,hei] with w hw hwi
    simpa only [ψ,hwi] using hw
  have Hpull (d v:Model n): fderiv ℝ (fderiv ℝ ψ) z d v+
      fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d v=
      fderiv ℝ (fderiv ℝ φ) 0 (R d) (R v)+normalHessian x p (R d) (R v):=by
    have hzF:fderiv ℝ (fun v=>φ v+c v) 0=0:=by
      rw [fderiv_fun_add (hφ.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hφD,(normalCost_hasFDerivAt_zero hp).fderiv]
      simp only [map_neg,add_neg_cancel]
    have HF:=second_fderiv_comp_stationary (f:=fun v=>φ v+c v) (g:=e)
      (he0.symm ▸ hφ.add hc) he2 (by rwa [he0]) d v
    rw [he0,second_fderiv_add_eq hφ hc] at HF
    have Heq:(fun w=>ψ w+chartCost a (riemannianExp x p) w)=ᶠ[𝓝 z]
        (fun w=>φ (e w)+c (e w)):=by
      filter_upwards [hce] with w hw
      rw [hw]
    have HH:=congrArg (fun A:Model n →L[ℝ] Model n →L[ℝ] ℝ=>A d v) Heq.fderiv.fderiv_eq
    rw [second_fderiv_add_eq hψ hcc] at HH
    exact HH.trans HF
  have hRp: (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).comp R=
      ContinuousLinearMap.id ℝ (Model n):=by
    let f: E → Model n := (extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x
    have hf:ContDiffAt ℝ ∞ f 0:=chart_normal_smooth (by simpa only [riemannianExp_zero] using hx)
    have hid:(fun w=>f (e w))=ᶠ[𝓝 z] (fun w=>w):=by
      filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds
        ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)] with w hw ht
      simp only [f,Function.comp_apply,hw,(extChartAt 𝓘(ℝ,Model n) a).right_inv ht]
    have HD:=hid.fderiv_eq (𝕜:=ℝ)
    rw [fderiv_fun_comp z (by simpa only [he0] using hf.differentiableAt (by simp))
      (he.differentiableAt (by simp)),he0,fderiv_fun_id] at HD
    exact HD
  have hRdet:chartJacobian (n:=n) a x*R.toLinearMap.normDet=1:=by
    have hh:=congrArg (fun F:Model n →L[ℝ] Model n=>F.toLinearMap.normDet) hRp
    rw [show (ContinuousLinearMap.id ℝ (Model n)).toLinearMap=LinearMap.id by rfl,
      LinearMap.normDet_id] at hh
    change ((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).toLinearMap ∘ₗ
      R.toLinearMap).normDet=1 at hh
    erw [LinearMap.normDet_comp_of_finrank_eq R.toLinearMap
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).toLinearMap rfl] at hh
    rwa [normDet_chart_exp_zero a x hx] at hh
  refine ⟨ψ,R,hψ,?_,?_,?_,hψlo,?_,hRdet,?_⟩
  · rwa [hψD]
  · rwa [hψD]
  · change u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ (e z)
    rw [he0]
    exact ((congrArg u ((extChartAt 𝓘(ℝ,Model n) a).left_inv hx)).trans hval)
  · refine ⟨m*k,mul_pos hm hk,fun d=>?_⟩
    rw [Hpull]
    simp only [hessianValue_eq_normalHessian hp] at hpos
    calc
      _ = m*(k*‖d‖^2):=by ring
      _ ≤ m*‖R d‖^2:=mul_le_mul_of_nonneg_left (Hk d) hm.le
      _ ≤ _:=hpos (R d)
  · apply ContinuousLinearMap.ext
    intro d
    apply ext_inner_right ℝ
    intro v
    simp only [bilinearOperator_inner,add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    exact Hpull d v

end NormalTestChart
end WeakMTWTransport

end
end

end OAI
