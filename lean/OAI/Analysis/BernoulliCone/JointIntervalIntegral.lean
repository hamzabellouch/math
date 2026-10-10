import OAI.Analysis.BernoulliCone.LocalFluxExtensions

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- A compact-interval parameter derivative, with domination obtained from C1
on an actual compact product. No derivative bound is an extra premise. -/
theorem fixed_hasFDerivAt {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) (x:E) (a b:ℝ) :
    HasFDerivAt (fun y:E=>∫t in a..b,F (y,t))
      (∫t in a..b,fderiv ℝ F (x,t) ∘L ContinuousLinearMap.inl ℝ E ℝ) x := by
  let D:E×ℝ→E→L[ℝ] G:=fun p=>fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ
  have hD:Continuous D:=(hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hc:IsCompact ((Metric.closedBall x 1)×ˢ(uIcc a b)):=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C,hC⟩:=hc.exists_bound_of_continuousOn hD.continuousOn
  have hFu (y:E):Continuous (fun t:ℝ=>F (y,t)):=hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hDu (y:E):Continuous (fun t:ℝ=>D (y,t)):=hD.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun y t=>F (y,t)) (F':=fun y t=>D (y,t))
    (s:=Metric.closedBall x 1) (bound:=fun _=>C) (Metric.closedBall_mem_nhds x (by norm_num))
  · exact .of_forall fun y=>(hFu y).aestronglyMeasurable
  · exact (hFu x).intervalIntegrable a b
  · exact (hDu x).aestronglyMeasurable
  · exact ae_of_all _ fun t ht y hy=>hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ y _=>by
      have hi:HasFDerivAt (fun z:E=>(z,t)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
        simpa only [ContinuousLinearMap.inl,id_eq] using
          (hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const t y)
      exact ((hF.differentiable (by norm_num)) (y,t)).hasFDerivAt.comp y hi

def heightPrimitive (F:E×ℝ→G) (p:E×ℝ) : G := ∫s in (0:ℝ)..p.2,F (p.1,s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace G] in
lemma heightPrimitive_rescale (F:E×ℝ→G) (p:E×ℝ) :
    heightPrimitive F p=∫s in (0:ℝ)..1,p.2 • F (p.1,s*p.2) := by
  by_cases ht:p.2=0
  · simp [heightPrimitive,ht]
  · rw [intervalIntegral.integral_smul]
    have hh:=intervalIntegral.integral_comp_mul_right (a:=0) (b:=1) (fun s:ℝ=>F (p.1,s)) ht
    rw [hh]
    simp only [zero_mul,one_mul,smul_smul,mul_inv_cancel₀ ht,one_smul,heightPrimitive]

omit [CompleteSpace G] in
/-- Joint differentiability is proved, rather than inferred from separate
partial derivatives. Rescaling to [0,1] gives a compact dominated derivative. -/
theorem heightPrimitive_differentiable [CompleteSpace G] {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    Differentiable ℝ (heightPrimitive F) := by
  let B:(E×ℝ)×ℝ→G:=fun z=>z.1.2 • F (z.1.1,z.2*z.1.2)
  have hB:ContDiff ℝ 1 B:=by
    have hm:ContDiff ℝ 1 (fun z:(E×ℝ)×ℝ=>(z.1.1,z.2*z.1.2)):=by fun_prop
    exact (contDiff_fst.snd).smul (hF.comp hm)
  intro p
  have hd: DifferentiableAt ℝ (fun y:E×ℝ=>∫s in (0:ℝ)..1,B (y,s)) p :=
    (fixed_hasFDerivAt hB p 0 1).differentiableAt
  exact hd.congr_of_eventuallyEq (.of_forall fun q=>heightPrimitive_rescale F q)

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma heightPrimitive_height {F:E×ℝ→G} (hF:Continuous F) (p:E×ℝ) :
    HasDerivAt (fun t:ℝ=>heightPrimitive F (p.1,t)) (F p) p.2 := by
  have hc:Continuous (fun t:ℝ=>F (p.1,t)):=hF.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 p.2)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
lemma heightPrimitive_fderiv {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) (p:E×ℝ) (v:E) (r:ℝ) :
    fderiv ℝ (heightPrimitive F) p (v,r)=
      (∫s in (0:ℝ)..p.2,fderiv ℝ F (p.1,s) (v,0))+r • F p := by
  have hd:HasFDerivAt (heightPrimitive F) (fderiv ℝ (heightPrimitive F) p) p:=
    (heightPrimitive_differentiable hF p).hasFDerivAt
  have hi:HasFDerivAt (fun y:E=>(y,p.2)) (ContinuousLinearMap.inl ℝ E ℝ) p.1:=by
    simpa only [ContinuousLinearMap.inl,id_eq] using
      (hasFDerivAt_id (𝕜:=ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have he: fderiv ℝ (heightPrimitive F) p ∘L ContinuousLinearMap.inl ℝ E ℝ=
      ∫s in (0:ℝ)..p.2,fderiv ℝ F (p.1,s) ∘L ContinuousLinearMap.inl ℝ E ℝ :=
    (HasFDerivAt.comp (g:=heightPrimitive F) (f:=fun y:E=>(y,p.2)) p.1 hd hi).unique
      (fixed_hasFDerivAt hF p.1 0 p.2)
  have hx:=congrArg (fun L:E→L[ℝ] G=>L v) he
  have hDc:Continuous (fun s:ℝ=>fderiv ℝ F (p.1,s) ∘L ContinuousLinearMap.inl ℝ E ℝ):=
    ((hF.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  rw [ContinuousLinearMap.intervalIntegral_apply (hDc.intervalIntegrable 0 p.2)] at hx
  have hh:=hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have ht:fderiv ℝ (heightPrimitive F) p (0,1)=F p:=hh.unique (heightPrimitive_height hF.continuous p)
  calc
    _=fderiv ℝ (heightPrimitive F) p ((v,0)+r • ((0:E),(1:ℝ))) := by congr 1; ext <;> simp
    _=fderiv ℝ (heightPrimitive F) p (v,0)+r • fderiv ℝ (heightPrimitive F) p (0,1) := by rw [map_add,map_smul]
    _=_ := by rw [ht]; exact congrArg (·+r • F p) hx

lemma graph_fderiv {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) {u:E→ℝ} {x:E}
    (hu:DifferentiableAt ℝ u x) (v:E) :
    fderiv ℝ (fun y:E=>heightPrimitive F (y,u y)) x v=
      (∫s in (0:ℝ)..u x,fderiv ℝ F (x,s) (v,0))+fderiv ℝ u x v • F (x,u x) := by
  have hh:HasFDerivAt (fun y:E=>heightPrimitive F (y,u y))
      (fderiv ℝ (heightPrimitive F) (x,u x) ∘L
        (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ u x)) x :=
    HasFDerivAt.comp (g:=heightPrimitive F) (f:=fun y:E=>(y,u y)) x
      (heightPrimitive_differentiable hF (x,u x)).hasFDerivAt
      ((hasFDerivAt_id x).prodMk hu.hasFDerivAt)
  rw [hh.fderiv]
  exact heightPrimitive_fderiv hF (x,u x) v (fderiv ℝ u x v)
end Bernoulli.ParametricIntegral

end
end

end OAI
