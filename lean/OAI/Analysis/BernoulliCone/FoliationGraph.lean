import OAI.Analysis.BernoulliCone.JointIntervalIntegral

namespace OAI

universe uE

section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.Foliation
open ParametricIntegral
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma divergence_graph_primitive {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) :
    divergence (fun y:E=>heightPrimitive A (y,u y)) x=
      (∫s in (0:ℝ)..u x,divergence (fun y:E=>A (y,s)) x)+
        inner ℝ (A (x,u x)) (gradient u x) := by
  let e:=stdOrthonormalBasis ℝ E
  have hc:Continuous (fun s:ℝ=>fderiv ℝ A (x,s)):=
    (hA.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
  have hci (i):Continuous (fun s:ℝ=>inner ℝ (e i) (fderiv ℝ A (x,s) (e i,0))):=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hi (s:ℝ) (v:E):fderiv ℝ (fun y:E=>A (y,s)) x v=fderiv ℝ A (x,s) (v,0):=by
    rw [(sliceLeft_hasFDerivAt ((hA.differentiable (by norm_num)) (x,s))).fderiv]
    simp
  have he (v:E):inner ℝ v (∫s in (0:ℝ)..u x,fderiv ℝ A (x,s) (v,0))=
      ∫s in (0:ℝ)..u x,inner ℝ v (fderiv ℝ A (x,s) (v,0)) :=
    ((innerSL ℝ v).intervalIntegral_comp_comm
      ((hc.clm_apply continuous_const).intervalIntegrable 0 (u x))).symm
  rw [divergence]
  simp_rw [graph_fderiv hA hu,inner_add_right,real_inner_smul_right,he]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [←intervalIntegral.integral_finsetSum (fun i _=>(hci i).intervalIntegrable 0 (u x))]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [divergence,hi]
    rfl
  · simp_rw [←inner_gradient_left]
    rw [(stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
    exact real_inner_comm _ _
lemma continuous_spatial_divergence {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) :
    Continuous (fun s:ℝ=>divergence (fun y:E=>A (y,s)) x) := by
  have hc:Continuous (fun s:ℝ=>fderiv ℝ A (x,s)):=
    (hA.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
  have hi (s:ℝ) (v:E):fderiv ℝ (fun y:E=>A (y,s)) x v=fderiv ℝ A (x,s) (v,0):=by
    rw [(sliceLeft_hasFDerivAt ((hA.differentiable (by norm_num)) (x,s))).fderiv]
    simp
  simp only [divergence,hi]
  exact continuous_finsetSum _ (fun i _=>continuous_const.inner (hc.clm_apply continuous_const))

/-- Integrating the nonlinear bulk inequality gives exactly the flux difference.
This is FTC and parameter differentiation, not a postulated graph comparison. -/
lemma integrated_bulk {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) {a b:ℝ} (hab:a≤b)
    (hbulk:∀s∈Icc a b,divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    2*(∫s in a..b,divergence (fun y:E=>A (y,s)) x)≤‖A (x,a)‖^2-‖A (x,b)‖^2 := by
  have hAC:ContDiff ℝ 1 (fun s:ℝ=>A (x,s)):=hA.comp (contDiff_const.prodMk contDiff_id)
  have hDC:Continuous (deriv (fun t:ℝ=>A (x,t))) := hAC.continuous_deriv (by norm_num)
  have hAD(s:ℝ):HasDerivAt (fun t:ℝ=>A (x,t)) (deriv (fun t:ℝ=>A (x,t)) s) s:=
    (hAC.differentiable (by norm_num) s).hasDerivAt
  have hN(s:ℝ):HasDerivAt (fun t:ℝ=>‖A (x,t)‖^2)
      (2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)) s:=by
    simpa only [real_inner_self_eq_norm_sq,real_inner_comm (deriv (fun t:ℝ=>A (x,t)) s),two_mul] using
      (hAD s).inner ℝ (hAD s)
  have hc:Continuous (fun s:ℝ=>2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)):=
    continuous_const.mul (hAC.continuous.inner hDC)
  have hFTC:(∫s in a..b,2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s))=
      ‖A (x,b)‖^2-‖A (x,a)‖^2:=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hN s) (hc.intervalIntegrable a b)
  have hi:IntervalIntegrable (fun s:ℝ=>2*divergence (fun y:E=>A (y,s)) x) volume a b:=
    (continuous_const.mul (continuous_spatial_divergence hA x)).intervalIntegrable a b
  have hle:(∫s in a..b,2*divergence (fun y:E=>A (y,s)) x+
      2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s))≤0 := by
    have hh:=intervalIntegral.integral_mono_on hab (hi.add (hc.intervalIntegrable a b))
      (intervalIntegrable_const (c:=(0:ℝ))) (fun s hs=>by linarith [hbulk s hs])
    simpa using hh
  rw [intervalIntegral.integral_add hi (hc.intervalIntegrable a b),hFTC,
    intervalIntegral.integral_const_mul] at hle
  linarith
lemma divergence_smul_sub {f g:E→E} {x:E}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) (c:ℝ) :
    divergence (fun y=>c • (f y-g y)) x=c*(divergence f x-divergence g x) := by
  have hh:HasFDerivAt (fun y=>c • (f y-g y)) (c • (fderiv ℝ f x-fderiv ℝ g x)) x:=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).const_smul c
  rw [divergence,hh.fderiv]
  simp only [smul_apply,sub_apply,
    real_inner_smul_right,inner_sub_right,Finset.mul_sum,Finset.sum_sub_distrib,divergence,mul_sub]

def graphPotential (A:E×ℝ→E) (u v:E→ℝ) (x:E) : E :=
  (2:ℝ) • (heightPrimitive A (x,v x)-heightPrimitive A (x,u x))
lemma graph_potential_identity {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x) :
    divergence (graphPotential A u v) x=
      2*(∫s in u x..v x,divergence (fun y:E=>A (y,s)) x)+
        2*inner ℝ (A (x,v x)) (gradient v x)-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hd(w:E→ℝ)(hw:DifferentiableAt ℝ w x):
      DifferentiableAt ℝ (fun y:E=>heightPrimitive A (y,w y)) x:=
    DifferentiableAt.comp (f:=fun y:E=>(y,w y)) (g:=heightPrimitive A) x
      (heightPrimitive_differentiable hA (x,w x)) (differentiableAt_id.prodMk hw)
  unfold graphPotential
  rw [divergence_smul_sub (hd v hv) (hd u hu),
    divergence_graph_primitive hA hv,divergence_graph_primitive hA hu]
  have hi:=intervalIntegral.integral_interval_sub_left (μ:=volume)
    ((continuous_spatial_divergence hA x).intervalIntegrable 0 (v x))
    ((continuous_spatial_divergence hA x).intervalIntegrable 0 (u x))
  rw [←hi]
  ring

lemma graph_potential_bulk_bound {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (huv:u x≤v x)
    (hbulk:∀s∈Icc (u x) (v x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    divergence (graphPotential A u v) x≤‖gradient v x‖^2+
      ‖A (x,u x)‖^2-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hi:=integrated_bulk hA x huv hbulk
  have hs:0≤‖gradient v x-A (x,v x)‖^2:=sq_nonneg _
  rw [norm_sub_sq_real] at hs
  have he:inner ℝ (gradient v x) (A (x,v x))=inner ℝ (A (x,v x)) (gradient v x):=real_inner_comm _ _
  rw [he] at hs
  rw [graph_potential_identity hA hu hv]
  linarith
end Bernoulli.Foliation

end
end

end OAI
