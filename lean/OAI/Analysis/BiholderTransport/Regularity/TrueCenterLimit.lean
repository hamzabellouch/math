import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterRayLimit
import OAI.Analysis.BiholderTransport.Coordinates.ExpJacContinuity
import OAI.Analysis.BiholderTransport.Calculus.TrueCenterJet
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearGainLimit

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance trueLimitFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance trueLimitDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance trueLimitDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance trueLimitBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance trueLimitBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma exists_true_center_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ),
    ∀J:(j:ℕ) → TrueCenterJet (n:=n) u a c (φ j) (lj j),
    ∀(l κ χ:ℝ) (q r:Model n) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    l∈U → 0<l → l<1 → 0<χ →
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
    Tendsto lj atTop (𝓝 l) →
    Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
    Tendsto (fun j=>(J j).q) atTop (𝓝 q) →
    Tendsto (fun j=>(J j).fullRay) atTop (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>(J j).curvature) atTop (𝓝 κ) →
    Tendsto (fun j=>(J j).matrix) atTop (𝓝 H) →
    (∀ᶠ j in atTop,χ≤expJacobian (J j).y (J j).p*
      (normalHessianOperator (J j).y (J j).p+(J j).A).det) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_true_center_jet_gain (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u a c φ lj J l κ χ q r H hlu hl hl1 hχ hq hlj hb hqq hfull hκ hH hvol
  let P:=fun j (V:Model n →L[ℝ] Model n →L[ℝ] ℝ)=>
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
        (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2*
        (normalHessianOperator (J j).y (J j).p+(J j).A).det ∧
      ∀d,V d d+δ*(1-lj j)*frameMetric a (J j).b d d+
        ((J j).curvature/(lj j)^2)*(frameMetric a (J j).b (J j).q d)^2≤(J j).matrix d d
  have hpos:∀ᶠ j in atTop,0<lj j ∧ lj j<1:=hlj.eventually (Ioo_mem_nhds hl hl1)
  have hVe:∀ᶠ j in atTop,∃V,P j V:=by
    filter_upwards [hpos,hlj.eventually (hU.mem_nhds hlu)] with j hj hju
    exact Hδ _ hju hj.1 hj.2 u a c (φ j) (J j)
  let V:=fun j=>if h:∃V,P j V then Classical.choose h else 0
  have hV:∀ᶠ j in atTop,P j (V j):=hVe.mono (fun j hj=>by
    simpa only [V,dite_eq_left hj] using Classical.choose_spec hj)
  let G:=fun j=>frameMetric a (J j).b
  let G₀:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a)
  have hb0:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hG:Tendsto G atTop (𝓝 G₀):=(frameMetric_continuousAt hb0).tendsto.comp hb
  have hf:=tendsto_clm_apply hG hqq
  have hshort:Tendsto (fun j=>(J j).shortRay) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=chartRay_tendsto hb hqq
  have hs:=continuous_expJacobian.continuousAt.tendsto.comp hshort
  have ha:=continuous_expJacobian.continuousAt.tendsto.comp hfull
  have hfr: Tendsto (fun j=>(chartFiberInverse a (J j).b).toLinearMap.normDet) atTop
      (𝓝 (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet):=
    (frameNormDet_continuousAt hb0).tendsto.comp hb
  let k:=fun j=>(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
    (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2*χ
  have hk:Tendsto k atTop (𝓝 ((chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
      (expJacobian a q)^2*χ)):=(((hfr.pow 2).mul (hlj.pow n)).mul (hs.pow 2)).mul_const χ
  have hk0:0<(chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
      (expJacobian a q)^2*χ:=by
    have Hf:=frameNormDet_pos hb0
    have He:=expJacobian_pos_of_injectivityDomain hq
    positivity
  have HVe:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧
      (∀d,V j d d+(δ*(1-lj j))*G j d d+
        ((J j).curvature/(lj j)^2)*(G j (J j).q d)^2≤(J j).matrix d d) ∧
      0≤expJacobian (J j).fullRay.1 (J j).fullRay.2 ∧
      k j≤expJacobian (J j).fullRay.1 (J j).fullRay.2*(bilinearOperator (V j)).det:=by
    filter_upwards [hV,hpos,hvol] with j hj hljj hvolj
    refine ⟨hj.1,?_,hj.2.2.2,expJacobian_nonneg _ _,?_⟩
    · intro d
      by_cases hd:d=0
      · simp [hd]
      · exact (hj.2.1 d hd).le
    · rw [hj.2.2.1]
      have hfactor:0≤(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
          (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2:=by
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hljj.1.le _)) (sq_nonneg _)
      have HH:=mul_le_mul_of_nonneg_left hvolj hfactor
      dsimp only [k,TrueCenterJet.fullRay]
      convert HH using 1; first | rfl | ring
  have hbc:Tendsto (fun j=>δ*(1-lj j)) atTop (𝓝 (δ*(1-l))):=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hlj)
  have hcc:Tendsto (fun j=>(J j).curvature/(lj j)^2) atTop (𝓝 (κ/l^2)):=
    hκ.div (hlj.pow 2) (pow_ne_zero _ hl.ne')
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hgain,ha0,hdet⟩:=
    exists_bilinear_gain_limit hH hG hf ha hk hbc hcc hk0 HVe
  exact ⟨V₀,hVs,hVp,hgain,ha0,hdet⟩
end TrueCenterLimit
end WeakMTWTransport

end
end

end OAI
