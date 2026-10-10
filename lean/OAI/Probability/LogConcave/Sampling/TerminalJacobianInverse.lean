import Mathlib
import OAI.Probability.LogConcave.Sampling.TerminalMean
import OAI.Probability.LogConcave.Sampling.SpatialJacobianTimeDeriv

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

theorem terminalJacobian_inverse (t : Icc (0:ℝ) T) (y : Point d) :
    let C := fderiv ℝ (fun z => terminalBackward hF x hr.le hl hT0 hT1 (t,z)) y
    let B := terminalJacobian hF x hr hl hT0 hT1 (t,y)
    B.comp C=ContinuousLinearMap.id ℝ (Point d) ∧
      C.comp B=ContinuousLinearMap.id ℝ (Point d) := by
  dsimp only
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩
  have hf : Differentiable ℝ f :=
    (probabilityTransport_contDiff hF x hr.le hl hT0 hT1 _ _ 1).differentiable (by norm_num)
  have hg : Differentiable ℝ g :=
    (probabilityTransport_contDiff hF x hr.le hl hT0 hT1 _ _ 1).differentiable (by norm_num)
  have hfg : f ∘ g=id := by
    funext z
    exact (probabilityTransport_cocycle hF x hr.le hl hT0 hT1 _ _ _ z).trans
      (probabilityTransport_initial hF x hr.le hl hT0 hT1 t z)
  have hgf : g ∘ f=id := by
    funext z
    exact (probabilityTransport_cocycle hF x hr.le hl hT0 hT1 _ _ _ z).trans
      (probabilityTransport_initial hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ z)
  have he : (fun z => terminalBackward hF x hr.le hl hT0 hT1 (t,z))=f :=
    funext (terminalBackward_eq hF x hr.le hl hT0 hT1 t)
  rw [he,terminalJacobian_eq,terminalBackward_eq]
  change (fderiv ℝ g (f y)).comp (fderiv ℝ f y)=_ ∧
    (fderiv ℝ f y).comp (fderiv ℝ g (f y))=_
  constructor
  · rw [←fderiv_comp y (hg (f y)) (hf y),hgf]
    exact fderiv_id
  · have hid : g (f y)=y := congrFun hgf y
    nth_rw 1 [←hid]
    rw [←fderiv_comp (f y) (hf (g (f y))) (hg (f y)),hfg]
    exact fderiv_id

lemma terminalJacobian_final (y : Point d) :
    terminalJacobian hF x hr hl hT0 hT1 (T,y)=ContinuousLinearMap.id ℝ (Point d) := by
  rw [terminalJacobian_eq hF x hr hl hT0 hT1 ⟨T,hT0,le_rfl⟩]
  have he : probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ ⟨T,hT0,le_rfl⟩=id :=
    funext (probabilityTransport_initial hF x hr.le hl hT0 hT1 _)
  rw [he]
  exact fderiv_id
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

include hlam

theorem terminalJacobian_deriv {ρ : ℝ} (hρ0 : 0<ρ) (hρT : ρ<T) (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0 hT1 (u,y))
      ((r*ρ) • (terminalJacobian hF x hr hl hT0 hT1 (ρ,y)).comp
        (conditionalFirstJet F x r ((lam:ℝ)*r)
          (ρ,terminalBackward hF x hr.le hl hT0 hT1 (ρ,y)))) ρ := by
  let X := terminalBackward hF x hr.le hl hT0 hT1
  let B := fun u => terminalJacobian hF x hr hl hT0 hT1 (u,y)
  let C := fun u => fderiv ℝ (fun z => X (u,z)) y
  let U := conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,X (ρ,y))
  let K := (-r*ρ) • U
  let B' := fderiv ℝ (terminalJacobian hF x hr hl hT0 hT1) (ρ,y) (1,0)
  have hX : ContDiff ℝ (⊤:ℕ∞) X := terminalBackward_smooth hF x hr.le hl hT0 hT1
  have hY : Differentiable ℝ (fun z => X (ρ,z)) :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hM := (conditionalFieldMean_smooth hF x hr.le hl hρ0.le (hρT.trans hT1)).differentiable (by simp)
  have hV : Differentiable ℝ (fun z => -r • conditionalFieldMean F x r ρ z) :=
    hM.const_smul (-r)
  have hK : fderiv ℝ (fun z => -r • conditionalFieldMean F x r ρ z) (X (ρ,y))=K := by
    rw [fderiv_fun_const_smul (hM (X (ρ,y))) (-r),conditionalFirstJet_deriv hF x hr hlam hl hρ0.le (hρT.trans hT1)]
    simp only [K,U,smul_smul]
  have hC : HasDerivAt C (K.comp (C ρ)) ρ := by
    have hh := spatialJacobian_time_deriv hX
      (fun z => -r • conditionalFieldMean F x r ρ z) ρ
      (fun z => terminalBackward_deriv hF x hr hl hT0 hT1 hρ0 hρT z) y
    change HasDerivAt C (fderiv ℝ ((fun z => -r • conditionalFieldMean F x r ρ z) ∘
      (fun z => X (ρ,z))) y) ρ at hh
    rw [fderiv_comp y (hV (X (ρ,y))) (hY y),hK] at hh
    exact hh
  have hB : HasDerivAt B B' ρ := by
    have hh := ((terminalJacobian_smooth hF x hr hl hT0 hT1).differentiable (by simp) (ρ,y)).hasFDerivAt.comp_hasDerivAt ρ
      ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y))
    simpa only [B,B',Function.comp_def,id_eq] using hh
  have he : (fun u => (B u).comp (C u))=ᶠ[nhds ρ] fun _ => ContinuousLinearMap.id ℝ (Point d) := by
    filter_upwards [Ioo_mem_nhds hρ0 hρT] with u hu
    exact (terminalJacobian_inverse hF x hr hl hT0 hT1 ⟨u,hu.1.le,hu.2.le⟩ y).1
  have hz := (hB.clm_comp hC).unique
    ((hasDerivAt_const ρ (ContinuousLinearMap.id ℝ (Point d))).congr_of_eventuallyEq he)
  have hCB : (C ρ).comp (B ρ)=ContinuousLinearMap.id ℝ (Point d) :=
    (terminalJacobian_inverse hF x hr hl hT0 hT1 ⟨ρ,hρ0.le,hρT.le⟩ y).2
  have hlin := congrArg (fun A : Point d →L[ℝ] Point d => A.comp (B ρ)) hz
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_assoc,hCB,
    ContinuousLinearMap.comp_id,ContinuousLinearMap.zero_comp] at hlin
  have hB' : B'=(r*ρ) • (B ρ).comp U := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun A : Point d →L[ℝ] Point d => A v) (eq_neg_of_add_eq_zero_left hlin)
    simpa only [K,neg_apply,ContinuousLinearMap.comp_apply,smul_apply,
      map_smul,map_neg,neg_mul,neg_smul,neg_neg] using hv
  exact hB' ▸ hB
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam

theorem terminalJacobian_deriv_closed (ρ : Icc (0:ℝ) T) (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0.le hT1 (u,y))
      ((r*(ρ:ℝ)) • steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) ρ := by
  let B := terminalJacobian hF x hr hl hT0.le hT1
  let G := fun u => fderiv ℝ B (u,y) (1,0)
  let H := fun u => (r*u) • steinIntegrand hF x hr hl hT0.le hT1 (u,y)
  have hB : ContDiff ℝ (⊤:ℕ∞) B := terminalJacobian_smooth hF x hr hl hT0.le hT1
  have hBs : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hG : Continuous G :=
    ((hBs.continuous.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hH : Continuous H :=
    (continuous_const.mul continuous_id).smul
      ((steinIntegrand_smooth hF x hr hlam hl hT0.le hT1).continuous.comp (continuous_id.prodMk continuous_const))
  have hD (u : ℝ) : HasDerivAt (fun t => B (t,y)) (G u) u := by
    have hh := (hB.differentiable (by simp) (u,y)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))
    simpa only [G,Function.comp_def,id_eq] using hh
  have he : EqOn G H (Ioo 0 T) := by
    intro u hu
    have hd := (hD u).unique (terminalJacobian_deriv hF x hr hlam hl hT0.le hT1 hu.1 hu.2 y)
    simpa only [B,H,steinIntegrand,smoothTimeClip_eq hT0.le hT1 ⟨hu.1.le,hu.2.le⟩] using hd
  have hz : G ρ=H ρ := he.closure hG hH (by rw [closure_Ioo hT0.ne]; exact ρ.2)
  have hh := hD (ρ:ℝ)
  rw [hz] at hh
  simpa only [B,H] using hh

lemma terminalJacobian_initial_deriv (y : Point d) :
    HasDerivAt (fun u => terminalJacobian hF x hr hl hT0.le hT1 (u,y)) 0 0 := by
  have hh := terminalJacobian_deriv_closed hF x hr hlam hl hT0 hT1 ⟨0,le_rfl,hT0.le⟩ y
  convert hh using 1
  ext v
  simp only [mul_zero,smul_apply,zero_smul,zero_apply]

lemma terminalJacobian_action_initial_deriv (y v : Point d) :
    HasDerivAt (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v) 0 0 := by
  have hh := ((terminalJacobian_initial_deriv hF x hr hlam hl hT0 hT1 y).sub
    (hasDerivAt_const 0 (ContinuousLinearMap.id ℝ (Point d)))).clm_apply (hasDerivAt_const 0 v)
  simpa only [Pi.sub_apply,sub_zero,zero_apply,map_zero,add_zero] using hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped NNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam

theorem terminalJacobian_action_deriv (ρ : Icc (0:ℝ) T) (y v : Point d) :
    HasDerivAt (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v)
      ((r*(ρ:ℝ)) • (steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) v) ρ := by
  have hh := ((terminalJacobian_deriv_closed hF x hr hlam hl hT0 hT1 ρ y).sub
    (hasDerivAt_const (ρ:ℝ) (ContinuousLinearMap.id ℝ (Point d)))).clm_apply
      (hasDerivAt_const (ρ:ℝ) v)
  simpa only [Pi.sub_apply,sub_zero,smul_apply,map_zero,add_zero] using hh

theorem terminalJacobian_action_quotient (ρ : Ioc (0:ℝ) T) (y v : Point d) :
    (ρ:ℝ)⁻¹ • deriv (fun u => (terminalJacobian hF x hr hl hT0.le hT1 (u,y)-
      ContinuousLinearMap.id ℝ (Point d)) v) ρ =
      r • (steinIntegrand hF x hr hl hT0.le hT1 (ρ,y)) v := by
  rw [(terminalJacobian_action_deriv hF x hr hlam hl hT0 hT1
    ⟨(ρ:ℝ),ρ.2.1.le,ρ.2.2⟩ y v).deriv,smul_smul]
  congr 1
  have hρ : (ρ:ℝ)≠0 := ne_of_gt ρ.2.1
  field_simp

theorem terminalJacobian_action_quotient_limit (y v : Point d) :
    Tendsto (fun u : ℝ => u⁻¹ • deriv (fun t =>
      (terminalJacobian hF x hr hl hT0.le hT1 (t,y)-
        ContinuousLinearMap.id ℝ (Point d)) v) u)
      (nhdsWithin 0 (Ioi 0))
      (nhds (r • (steinIntegrand hF x hr hl hT0.le hT1 (0,y)) v)) := by
  have hc : Continuous (fun u : ℝ => r • (steinIntegrand hF x hr hl hT0.le hT1 (u,y)) v) :=
    (((steinIntegrand_smooth hF x hr hlam hl hT0.le hT1).continuous.comp
      (continuous_id.prodMk continuous_const)).clm_apply continuous_const).const_smul r
  apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    (show Iio T ∈ nhdsWithin (0:ℝ) (Ioi 0) from
      nhdsWithin_le_nhds (Iio_mem_nhds hT0))] with u hu huT
  exact (terminalJacobian_action_quotient hF x hr hlam hl hT0 hT1 ⟨u,hu,huT.le⟩ y v).symm
end LogConcaveSampling

end

end

end

end OAI
