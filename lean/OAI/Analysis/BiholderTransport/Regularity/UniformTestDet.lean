import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SmoothTestPDE
import OAI.Analysis.BiholderTransport.Regularity.CenteredQuadratic
import OAI.Analysis.BiholderTransport.Contact.ContactJetCalculus

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction NNReal

namespace WeakMTWTransport
section UniformTestDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance uTDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance uTDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance uTBilinGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance uTBilinSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance uTPairGroup : NormedAddCommGroup (Model n × (Model n →L[ℝ] ℝ)) := inferInstance
local instance uTPairSpace : NormedSpace ℝ (Model n × (Model n →L[ℝ] ℝ)) := inferInstance
local instance uTMapGroup : NormedAddCommGroup (Model n →L[ℝ] Model n × (Model n →L[ℝ] ℝ)) := inferInstance
local instance uTMapSpace : NormedSpace ℝ (Model n →L[ℝ] Model n × (Model n →L[ℝ] ℝ)) := inferInstance

lemma WeakMTW.strict_test_det_bound_on_charts
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) {a b : M} {U V : Set M}
    (hU : IsOpen U) (hUa : U⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hV : IsOpen V) (hVb : V⊆(extChartAt 𝓘(ℝ,Model n) b).source)
    {C D : ℝ≥0} (hD : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
      ((extChartAt 𝓘(ℝ,Model n) a) '' U))
    (hC : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) b) V)
    {z : Model n} (hz : z∈(extChartAt 𝓘(ℝ,Model n) a) '' U)
    {x0 : M} {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)}
    (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ : Model n → ℝ} (hφ : ContDiffAt ℝ 2 φ z)
    (hYz : coordinateBackward a (-1,z,fderiv ℝ φ z)∈V)
    (hpφ : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
    (hgap : ∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w)
    (hpos : ∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
    |(fderiv ℝ (chartTestContact a b φ) z).det|≤(cap/lam)*((C:ℝ)*(D:ℝ))^n := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  have hchart : χ '' U⊆χ.target := by
    rintro w ⟨x,hx,rfl⟩
    exact χ.map_source (hUa hx)
  have hzT : z∈χ.target := hchart hz
  have hUo : IsOpen (χ '' U) := by
    have he : χ '' U = χ.target ∩ χ.symm ⁻¹' U := by
      ext w
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨χ.map_source (hUa hx),by simpa only [mem_preimage,χ.left_inv (hUa hx)] using hx⟩
      · rintro ⟨hw,hwU⟩
        exact ⟨χ.symm w,hwU,χ.right_inv hw⟩
    rw [he]
    exact (continuousOn_extChartAt_symm a).isOpen_inter_preimage
      (isOpen_extChartAt_target a) hU
  obtain ⟨ε,hε,hgap⟩ := hgap
  obtain ⟨m,hm,hpos⟩ := hpos
  obtain ⟨r₂,hr₂,_,hmount⟩ := exists_test_mountains hzT hφ hpφ hm hpos
  let Y := fun w : Model n => coordinateBackward a (-1,w,fderiv ℝ φ w)
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hzT).continuousAt.comp
      (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk (continuousAt_id.prodMk
        (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt))
  have hYn : ∀ᶠ w : Model n in 𝓝 z,Y w∈V := hY.preimage_mem_nhds (hV.mem_nhds hYz)
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      ε*dist w z^2≤uv.1 (χ.symm w)-φ w ∧
      w∈χ '' U ∧ w∈Metric.ball z r₂ ∧ ContinuousAt φ w ∧ Y w∈V := by
    filter_upwards [hgap,hUo.mem_nhds hz,Metric.ball_mem_nhds z hr₂,
      hφ.eventually (by norm_num),hYn] with w hw h₁ h₂ hφw hYw
    exact ⟨hw,h₁,h₂,hφw.continuousAt,hYw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  obtain ⟨rho0,rho1,hrho0,hrho1,hmin⟩ := huv.2
  apply hmtw.lower_test_chart_det_bound hlam hcap hrho0 hrho1
    (densityDualClass_isDual huv) hmin hr hε
    (fun w hw => hchart (hrsub hw).2.1)
    (hD.mono (fun w hw => (hrsub hw).2.1)) hC
    (fun w hw => (hrsub hw).2.2.2.1.continuousWithinAt)
    hval (fun w hw => (hrsub hw).1) (S := chartTestContact a b φ) ?_ ?_
    ((chartTestContact_contDiffAt hzT hφ (hVb hYz)).hasStrictFDerivAt (by norm_num))
  · intro w hw
    have hy : Y w∈ψ.source := hVb (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    refine ⟨ψ.map_source hy,?_⟩
    change ψ.symm (ψ (Y w))∈V
    rw [ψ.left_inv hy]
    exact (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
  · intro w hw q hq
    have hy : Y w∈ψ.source := hVb (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    change φ w+cost (χ.symm w) (ψ.symm (ψ (Y w)))≤φ q+cost (χ.symm q) (ψ.symm (ψ (Y w)))
    rw [ψ.left_inv hy]
    exact hmount w (Metric.ball_subset_closedBall (hrsub (Metric.ball_subset_closedBall hw)).2.2.1)
      q (Metric.ball_subset_closedBall (hrsub hq).2.2.1)

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTestContact_fderiv_formula {a b:M} {z:Model n} {φ:Model n → ℝ}
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ:ContDiffAt ℝ 2 φ z)
    (hb:coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    fderiv ℝ (chartTestContact a b φ) z=
      (fderiv ℝ (coordinateContact a b) (z,fderiv ℝ φ z)).comp
        ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ (fderiv ℝ φ) z)) := by
  have hC : ContDiffAt ℝ ∞ (coordinateContact (n:=n) a b) (z,fderiv ℝ φ z) :=
    coordinateContact_contDiffAt (n:=n) (M:=M) (a:=a) (b:=b)
      (q:=(z,fderiv ℝ φ z)) hz hb
  exact fderiv_contact_c2 hC hφ

lemma WeakMTW.test_det_bound_on_charts
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) {a b : M} {U V : Set M}
    (hU : IsOpen U) (hUa : U⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hV : IsOpen V) (hVb : V⊆(extChartAt 𝓘(ℝ,Model n) b).source)
    {C D : ℝ≥0} (hD : LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
      ((extChartAt 𝓘(ℝ,Model n) a) '' U))
    (hC : LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) b) V)
    {z : Model n} (hz : z∈(extChartAt 𝓘(ℝ,Model n) a) '' U)
    {x0 : M} {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)}
    (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ : Model n → ℝ} (hφ : ContDiffAt ℝ 2 φ z)
    (hYz : coordinateBackward a (-1,z,fderiv ℝ φ z)∈V)
    (hpφ : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
    (hlo : ∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (hpos : ∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
    |(fderiv ℝ (chartTestContact a b φ) z).det|≤(cap/lam)*((C:ℝ)*(D:ℝ))^n := by
  obtain ⟨m,hm,hpos⟩:=hpos
  have hzT:z∈(extChartAt 𝓘(ℝ,Model n) a).target:=by
    obtain ⟨w,hw,rfl⟩:=hz
    exact (extChartAt 𝓘(ℝ,Model n) a).map_source (hUa hw)
  let q:Model n → ℝ:=fun w=>‖w-z‖^2/2
  let H:=fderiv ℝ (fderiv ℝ φ) z
  let Q:=fderiv ℝ (fderiv ℝ q) z
  let J:=fderiv ℝ (coordinateContact a b) (z,fderiv ℝ φ z)
  let F:ℝ → ℝ:=fun δ=>|(J.comp ((ContinuousLinearMap.id ℝ (Model n)).prod (H-δ • Q))).det|
  have hF:Continuous F:=continuous_contact_jet_det J H Q
  have hF0:F 0=|(fderiv ℝ (chartTestContact a b φ) z).det|:=by
    rw [chartTestContact_fderiv_formula hzT hφ (hVb hYz)]
    simp only [F,zero_smul,sub_zero,H,J]
  have Hbound:∀ δ:ℝ, 0<δ → δ < m → F δ≤(cap/lam)*((C:ℝ)*(D:ℝ))^n:=by
    intro δ hδ hδm
    let ψ:Model n → ℝ:=fun w=>φ w-δ*q w
    have hq:ContDiffAt ℝ 2 q z:=(centered_half_norm_sq_c2 z).contDiffAt
    have hψ:ContDiffAt ℝ 2 ψ z:=hφ.sub (contDiffAt_const.mul hq)
    have hψL:fderiv ℝ ψ z=fderiv ℝ φ z:=by
      rw [show ψ=(fun w=>φ w-δ*q w) from rfl,
        fderiv_fun_sub (hφ.differentiableAt (by norm_num))
          ((hq.differentiableAt (by norm_num)).const_mul _)]
      change fderiv ℝ φ z-fderiv ℝ (δ • q) z=_
      rw [fderiv_const_smul_field,Pi.smul_apply,centered_half_norm_sq_fderiv,smul_zero,sub_zero]
    have hψH:fderiv ℝ (fderiv ℝ ψ) z=H-δ • Q:=by
      ext d e
      rw [show ψ=(fun w=>φ w-δ*q w) from rfl,
        second_fderiv_sub hφ (contDiffAt_const.mul hq),second_fderiv_const_mul]
      rfl
    have hψpos:∃ k>0,∀ d:Model n,k*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ ψ z)))) z d d:=by
      refine ⟨m-δ,sub_pos.mpr hδm,fun d=>?_⟩
      rw [hψL,hψH]
      change (m-δ)*‖d‖^2≤H d d-δ*(Q d d)+_
      change (m-δ)*‖d‖^2≤H d d-δ*(fderiv ℝ (fderiv ℝ (fun w:Model n=>‖w-z‖^2/2)) z d d)+_
      rw [centered_half_norm_sq_second]
      linarith only [hpos d]
    have hgap:∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-ψ w:=by
      refine ⟨δ/2,by positivity,?_⟩
      filter_upwards [hlo] with w hw
      dsimp only [ψ,q]
      rw [dist_eq_norm]
      linarith only [hw]
    have HB:=hmtw.strict_test_det_bound_on_charts hlam hcap hU hUa hV hVb hD hC hz huv hψ
      (hψL.symm ▸ hYz) (hψL.symm ▸ hpφ) (by simpa only [ψ,q,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),zero_div,mul_zero,sub_zero] using hval)
      hgap hψpos
    rw [chartTestContact_fderiv_formula hzT hψ (by rw [hψL]; exact hVb hYz),hψL,hψH] at HB
    exact HB
  rw [←hF0]
  apply le_of_tendsto (hF.continuousAt.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hm)] with δ hδ hδm
  exact Hbound δ hδ hδm

end UniformTestDet
end WeakMTWTransport

end
end

end OAI
