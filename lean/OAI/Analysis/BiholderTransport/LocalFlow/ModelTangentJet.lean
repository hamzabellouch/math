import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CoordinateScalarSupport
import OAI.Analysis.BiholderTransport.Regularity.CenterFullPullback

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ModelTangentJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_frame_identity (a : M) (d : Model n) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a d=d := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma model_tangent_second_fderiv {a : M} {f : TangentSpace 𝓘(ℝ,Model n) a → ℝ}
    {q : Model n} (hf : ContDiffAt ℝ 2 f q) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (fun r : Model n=>f r)) q d e=
      fderiv ℝ (fderiv ℝ f) q d e := by
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a
  have hA (r : Model n) : A r=r := center_frame_identity a r
  have hz (r : Model n) : (0 : TangentSpace 𝓘(ℝ,Model n) a)+A r=r :=
    (zero_add (A r)).trans (hA r)
  have H := second_fderiv_comp_affine (E := Model n) (F := TangentSpace 𝓘(ℝ,Model n) a) (f := f) A 0 q
    (by simpa only [hz] using hf) d e
  have he : (fun h : Model n => f ((0 : TangentSpace 𝓘(ℝ,Model n) a)+A h))=
      (fun h : Model n => f h) := by funext h; rw [hz h]
  rw [he,hz q,hA d,hA e] at H
  exact H

omit [Nonempty M] in
lemma scalarCostSupport_endpoint_contDiffAt {a c : M}
    {q : TangentSpace 𝓘(ℝ,Model n) a} {r : TangentSpace 𝓘(ℝ,Model n) c}
    {v s : ℝ} {φ : ℝ → ℝ} (hr : s • r∈injectivityDomain c)
    (he : riemannianExp a q=c) (hφ : ContDiffAt ℝ 2 φ v) :
    ContDiffAt ℝ 2 (fun w=>scalarCostSupport φ v c r s (riemannianExp a w)) q := by
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨c,s • r⟩ : TangentBundle 𝓘(ℝ,Model n) M) hr
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z:M×M=>cost z.1 z.2) (riemannianExp a q,riemannianExp c (s • r)) := by
    rwa [he]
  have hpair : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) a)
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun w : TangentSpace 𝓘(ℝ,Model n) a => (riemannianExp a w,riemannianExp c (s • r))) q :=
    (contMDiff_riemannianExp_fiber a q).prodMk contMDiffAt_const
  have hcost : ContDiffAt ℝ ∞ (fun w : TangentSpace 𝓘(ℝ,Model n) a =>
      cost (riemannianExp a w) (riemannianExp c (s • r))) q :=
    (hC'.comp (g := fun z:M×M=>cost z.1 z.2) q hpair).contDiffAt
  have hf : ContDiffAt ℝ ∞ (fun w=>v+cost c (riemannianExp c (s • r))/s-
      cost (riemannianExp a w) (riemannianExp c (s • r))/s) q :=
    contDiffAt_const.sub (hcost.div_const s)
  have hval : v+cost c (riemannianExp c (s • r))/s-cost (riemannianExp a q) (riemannianExp c (s • r))/s=v := by
    rw [he,add_sub_cancel_right]
  exact (hval.symm ▸ hφ).comp q (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

omit [Nonempty M] in
lemma model_riemannianExp_continuous (a : M) :
    Continuous (fun w : Model n=>riemannianExp a w) := by
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a
  have H := (continuous_riemannianExp a).comp A.continuous
  have he : riemannianExp a ∘ A=(fun w : Model n=>riemannianExp a w) := by
    funext w
    exact congrArg (riemannianExp a) (center_frame_identity a w)
  rwa [he] at H

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateScalarSupport_center_value (c : M) (v s : ℝ) (φ : ℝ → ℝ)
    (r z : Model n) :
    coordinateScalarSupport c φ (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),z)=
      scalarCostSupport φ v c r s ((extChartAt 𝓘(ℝ,Model n) c).symm z) := by
  have hx := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  rw [coordinateScalarSupport_eq hx,hb,center_frame_identity]

omit [Nonempty M] in
lemma coordinate_support_endpoint_germ {a c : M} {q r : Model n}
    (v s : ℝ) (φ : ℝ → ℝ) (he : riemannianExp a q=c) :
    (fun w : Model n=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))=ᶠ[𝓝 q]
      (fun w : Model n=>scalarCostSupport φ v c r s (riemannianExp a w)) := by
  have hx := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  have hExp := (model_riemannianExp_continuous a).continuousAt (x := q)
  have hqc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [he]
    exact mem_extChartAt_source c
  have hsource := hExp.eventually ((isOpen_extChartAt_source c).mem_nhds hqc)
  filter_upwards [hsource] with w hw
  rw [coordinateScalarSupport_center_value,(extChartAt 𝓘(ℝ,Model n) c).left_inv hw]

omit [Nonempty M] in
lemma coordinate_support_endpoint_hessian {a c : M} {q r : Model n}
    {v s : ℝ} {φ : ℝ → ℝ}
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (he : riemannianExp a q=c) (hφ : ContDiffAt ℝ 2 φ v) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (fun w : Model n=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))) q d e=
      fderiv ℝ (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ,Model n) a=>
        scalarCostSupport φ v c r s (riemannianExp a w))) q d e := by
  rw [(coordinate_support_endpoint_germ v s φ he).fderiv.fderiv_eq]
  exact model_tangent_second_fderiv (scalarCostSupport_endpoint_contDiffAt hr he hφ) d e

omit [Nonempty M] in
lemma exists_uniform_coordinate_center_full_pullback :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 → ∀ a c : M,∀ r q : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
      riemannianExp c (l • r)=a → riemannianExp a q=c →
      ∀ (φ : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 φ v → deriv φ v=l → ∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 φ v/l^2)*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 ≤
        inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
          fderiv ℝ (fderiv ℝ (fun w : Model n=>coordinateScalarSupport c φ
            (((v,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)),
              extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))) q d d := by
  obtain ⟨c0,hc0,H⟩ := exists_uniform_center_full_pullback (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hl
  intro hl0 hl1 a c r q hr hq hac hca φ v hφ hd d
  rw [coordinate_support_endpoint_hessian
    (contracted_minimizer_mem_injectivityDomain hr (by linarith) (by linarith)) hca hφ,
    real_inner_self_eq_norm_sq]
  exact hl hl0 hl1 c a r q hr hq hac hca φ v hφ hd d

end ModelTangentJet
end WeakMTWTransport

end
end

end OAI
