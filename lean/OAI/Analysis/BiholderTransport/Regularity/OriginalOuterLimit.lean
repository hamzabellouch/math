import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterRayLimit
import OAI.Analysis.BiholderTransport.Coordinates.ExpJacContinuity
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearGainLimit
import OAI.Analysis.BiholderTransport.Calculus.ScalarSecond
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartOuterMatrix
import OAI.Analysis.BiholderTransport.Regularity.OuterDetCompact

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OriginalOuterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance originalOuterFinite (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance originalOuterComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
local instance originalOuterDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance originalOuterDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance originalOuterBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance originalOuterBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma WeakMTW.exists_original_outer_limit
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (Φ:ℝ×ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → ContDiff ℝ ∞ Φ →
      ∀(a:M) (bj pj:ℕ → Model n) (γj mj:ℕ → ℝ)
        (Lj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ)
        (γ m l κ:ℝ) (p:Model n) (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
      (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) → Tendsto pj atTop (𝓝 p) →
      Tendsto γj atTop (𝓝 γ) → Tendsto mj atTop (𝓝 m) → Tendsto Lj atTop (𝓝 L) →
      deriv (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=l →
      iteratedDeriv 2 (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=κ →
      1 < l → κ < 0 →
      (∀d,d≠0 → 0 < m*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2) →
      (∀ᶠ j in atTop,bj j∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
        StrictMono (fun s=>Φ (γj j,s)) ∧
        (chartRay a (bj j) (pj j)).2∈activeLogs ((fun s=>Φ (γj j,s)) ∘ uv.2)
          (chartRay a (bj j) (pj j)).1 ∧
        0 ≤ mj j ∧ (∀d e,Lj j d e=Lj j e d) ∧ (∀d,0 ≤ Lj j d d) ∧
        HasLowerSecondTaylor (fun d=>Φ (γj j,uv.2 (movingNormal a (bj j,pj j+d)))+
          ‖chartFiberInverse a (bj j) (pj j+d)‖^2/2) 0 (mj j • Lj j)) →
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
        (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
        (∀d,m*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2 ≤ V d d) ∧
        expJacobian (n:=n) (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
          (l⁻¹ • (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
          (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
            (expJacobian (n:=n) a p)^2 := by
  classical
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_chart_outer_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv Φ huv hΦ a bj pj γj mj Lj γ m l κ p L hmin hb hp hγ hm hL hd hdd hl hκneg hpos hgood
  let z:=fun j=>chartRay a (bj j) (pj j)
  let z₀:TangentBundle 𝓘(ℝ,Model n) M:=⟨a,p⟩
  let sj:=fun j=>uv.2 (riemannianExp (z j).1 (z j).2)
  let lj:=fun j=>deriv (fun s=>Φ (γj j,s)) (sj j)
  let κj:=fun j=>iteratedDeriv 2 (fun s=>Φ (γj j,s)) (sj j)
  have hz:Tendsto z atTop (𝓝 z₀):=chartRay_tendsto hb hp
  have he:Tendsto (fun j=>riemannianExp (z j).1 (z j).2) atTop (𝓝 (riemannianExp a p)):=
    (contMDiff_riemannianExp (n:=n) (M:=M)).continuous.continuousAt.tendsto.comp hz
  have hs:Tendsto sj atTop (𝓝 (uv.2 (riemannianExp a p))):=uv.2.continuous.continuousAt.tendsto.comp he
  have hlj:Tendsto lj atTop (𝓝 l):=by
    rw [←hd]
    exact ((continuous_scalar_family_deriv hΦ).tendsto (γ,uv.2 (riemannianExp a p))).comp (hγ.prodMk_nhds hs)
  have hκj:Tendsto κj atTop (𝓝 κ):=by
    rw [←hdd]
    have H:=((continuous_scalar_family_second hΦ).tendsto (γ,uv.2 (riemannianExp a p))).comp (hγ.prodMk_nhds hs)
    exact H
  have hl0:0 < l:=zero_lt_one.trans hl
  have hcur:∀ᶠ j in atTop,1 < lj j ∧ κj j < 0:=
    (hlj.eventually (lt_mem_nhds hl)).and (hκj.eventually (gt_mem_nhds hκneg))
  let P:=fun j (V:Model n →L[ℝ] Model n)=>
    (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧ (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
    (∀d,mj j*Lj j d d-(κj j/(lj j)^2)*(frameMetric a (bj j) (pj j) d)^2 ≤ inner ℝ (V d) d) ∧
    expJacobian (n:=n) (reverseRay (z j)).1 ((lj j)⁻¹ • (reverseRay (z j)).2)*V.det ≤
      (chartFiberInverse a (bj j)).toLinearMap.normDet^2*(lj j)^n*K*(expJacobian (n:=n) (z j).1 (z j).2)^2
  have hVe:∀ᶠ j in atTop,∃V,P j V:=by
    filter_upwards [hgood,hcur] with j hj hc
    have hf:ContDiff ℝ ∞ (fun s=>Φ (γj j,s)):=hΦ.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨V,hVs,hVp,hgain,_,_,hdet⟩:=HK x0 uv (fun s=>Φ (γj j,s)) huv hf.continuous
      hj.2.1 a (bj j) (pj j) hj.1 (lj j) hj.2.2.1
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
      (hf.differentiable (by norm_num) (sj j)).hasDerivAt hc.1 hc.2.le
      (mj j • Lj j) (fun d e=>by simp only [smul_apply,smul_eq_mul,hj.2.2.2.2.1])
      (fun d=>mul_nonneg hj.2.2.2.1 (hj.2.2.2.2.2.1 d)) hj.2.2.2.2.2.2
    exact ⟨V,hVs,hVp,hgain,hdet⟩
  let Vj:=fun j=>if h:∃V,P j V then Classical.choose h else 0
  have hVj:∀ᶠ j in atTop,P j (Vj j):=hVe.mono (fun j hj=>by
    simpa only [Vj,dite_eq_left hj] using Classical.choose_spec hj)
  let W:=fun j=>(innerSL ℝ).comp (Vj j)
  let G:=fun j=>frameMetric a (bj j)
  let G₀:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a)
  have hb0:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hG:Tendsto G atTop (𝓝 G₀):=(frameMetric_continuousAt hb0).tendsto.comp hb
  have hfc:=tendsto_clm_apply hG hp
  have hc:Tendsto (fun j=>κj j/(lj j)^2) atTop (𝓝 (κ/l^2)):=hκj.div (hlj.pow 2) (pow_ne_zero _ hl0.ne')
  let Bj:=fun j=>mj j • Lj j-(κj j/(lj j)^2) • (G j (pj j)).smulRight (G j (pj j))
  let B₀:=m • L-(κ/l^2) • (G₀ p).smulRight (G₀ p)
  have hB:Tendsto Bj atTop (𝓝 B₀):=(hm.smul hL).sub (hc.smul (rankForm_tendsto hfc))
  have hBpos:∀d,d≠0 → 0 < B₀ d d:=by
    intro d hd
    simpa only [B₀,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc] using hpos d hd
  let aj:=fun j=>expJacobian (n:=n) (reverseRay (z j)).1 ((lj j)⁻¹ • (reverseRay (z j)).2)
  let a₀:=expJacobian (n:=n) (reverseRay z₀).1 (l⁻¹ • (reverseRay z₀).2)
  have hreverse:=continuous_reverseRay.continuousAt.tendsto.comp hz
  have ha:Tendsto aj atTop (𝓝 a₀):=continuous_expJacobian.continuousAt.tendsto.comp
    (contMDiff_tangentScale.continuous.continuousAt.tendsto.comp ((hlj.inv₀ hl0.ne').prodMk_nhds hreverse))
  have ha0:0 < a₀:=expJacobian_pos_of_injectivityDomain
    (contracted_minimizer_mem_injectivityDomain (reverseRay_minimizing hmin)
      (inv_pos.mpr hl0) (inv_lt_one_of_one_lt₀ hl))
  have hσ:=continuous_expJacobian.continuousAt.tendsto.comp hz
  have hfr: Tendsto (fun j=>(chartFiberInverse a (bj j)).toLinearMap.normDet) atTop
      (𝓝 (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet):=
    (frameNormDet_continuousAt hb0).tendsto.comp hb
  let kj:=fun j=>(chartFiberInverse a (bj j)).toLinearMap.normDet^2*(lj j)^n*K*(expJacobian (z j).1 (z j).2)^2
  have hk:Tendsto kj atTop (𝓝 ((chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*(expJacobian a p)^2)):=
    (((hfr.pow 2).mul (hlj.pow n)).mul_const K).mul (hσ.pow 2)
  have HW:∀ᶠ j in atTop,(∀d e,W j d e=W j e d) ∧ (∀d,0 ≤ W j d d) ∧
      (∀d,Bj j d d≤W j d d) ∧ aj j*(bilinearOperator (W j)).det≤kj j:=by
    filter_upwards [hVj] with j hj
    have hw (d e:Model n):W j d e=inner ℝ (Vj j d) e:=rfl
    refine ⟨?_,?_,?_,?_⟩
    · intro d e
      rw [hw,hw,hj.1,real_inner_comm]
    · intro d
      rw [hw]
      by_cases hd:d=0
      · simp [hd]
      · exact (hj.2.1 d hd).le
    · intro d
      simpa only [Bj,sub_apply,smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc,hw] using hj.2.2.1 d
    · have hW:bilinearOperator (W j)=Vj j:=by
        apply ContinuousLinearMap.ext
        intro d
        apply ext_inner_right ℝ
        intro e
        exact bilinearOperator_inner _ _ _
      rw [hW]
      exact hj.2.2.2
  obtain ⟨V,σ,hσ,HV,hVs,hVp,hgain,hdet⟩:=exists_outer_matrix_limit hB ha hk ha0 hBpos HW
  refine ⟨V,hVs,hVp,?_,hdet⟩
  intro d
  simpa only [B₀,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc] using hgain d
end OriginalOuterLimit
end WeakMTWTransport

end
end

end OAI
