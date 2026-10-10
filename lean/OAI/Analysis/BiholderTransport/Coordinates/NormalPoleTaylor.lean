import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiniteActiveGrowth
import OAI.Analysis.BiholderTransport.LinearAlgebra.LowerTaylor
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TaylorUniqueness
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma HasSecondTaylor.hasFDerivAt' {f:E → ℝ} {l:E →L[ℝ] ℝ} {H:E →L[ℝ] E →L[ℝ] ℝ}
    (hf:HasSecondTaylor f l H) : HasFDerivAt f l 0 := by
  have hNorm : (fun offset : E => ‖offset‖) =o[𝓝 0] (fun _ => (1:ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by
      simpa only [norm_zero] using continuous_norm.tendsto (0:E))
  have hSquare : (fun offset : E => ‖offset‖^2) =o[𝓝 0]
      (fun offset : E => ‖offset‖) := by
    simpa only [pow_two,one_mul] using
      hNorm.mul_isBigO (Asymptotics.isBigO_refl (fun offset : E => ‖offset‖) (𝓝 0))
  have hBilinear : (fun offset : E => H offset offset) =o[𝓝 0]
      (fun offset : E => ‖offset‖) :=
    (bilinear_isBigO_norm_mul (𝓝 (0:E)) H (fun offset => offset)
      (fun offset => offset)).trans_isLittleO
      (by simpa only [pow_two] using hSquare)
  have hQuadratic : (fun offset : E => H offset offset/2) =o[𝓝 0]
      (fun offset : E => ‖offset‖) := by
    simpa only [div_eq_mul_inv,mul_comm] using hBilinear.const_mul_left (2:ℝ)⁻¹
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [zero_add,sub_add_cancel] using
    ((hf.trans_isBigO hSquare.isBigO).add hQuadratic).of_norm_right

omit [FiniteDimensional ℝ E] in
lemma HasSecondTaylor.diagonal_unique' {f:E → ℝ} {l k:E →L[ℝ] ℝ}
    {H K:E →L[ℝ] E →L[ℝ] ℝ} (hf:HasSecondTaylor f l H) (hg:HasSecondTaylor f k K) (d:E) :
    H d d=K d d := by
  have he:=hf.hasFDerivAt'.unique hg.hasFDerivAt'
  subst k
  exact hf.diagonal_unique hg d
end TaylorUniqueness
section NormalPoleTaylor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFinitePole (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance tangentCompletePole (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

omit [Nonempty M] in
lemma normal_stationary_pole_taylor {f:M → ℝ} {x y:M}
    {r:TangentSpace 𝓘(ℝ,Model n) y} {q:TangentSpace 𝓘(ℝ,Model n) x}
    (hr:r∈injectivityDomain y) (hq:q∈injectivityDomain x)
    (hyx:riemannianExp y r=x)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    HasSecondTaylor (fun h=>f (riemannianExp x (q+h))+‖q+h‖^2/2) 0
      (pullBilinear (((innerSL ℝ).comp S : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)+normalHessian y r) (fderiv ℝ R q)) := by
  let C:=normalCost y r
  have hc:ContDiffAt ℝ 2 C 0:=
    (normalCost_contDiffAt hr).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hct:HasSecondTaylor C (innerSL ℝ (-r)) (normalHessian y r):=by
    simpa only [C,(normalCost_hasFDerivAt_zero hr).fderiv,normalHessian] using
      hasSecondTaylor_of_contDiffAt hc
  have H:HasSecondTaylor (fun h=>f (riemannianExp y h)+C h) 0
      (((innerSL ℝ).comp S : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)+normalHessian y r):=by
    simpa only [map_neg,add_neg_cancel] using hS.hasSecondTaylor'.add hct
  have ha:HasFDerivAt (fun h=>R (q+h)) (fderiv ℝ R q) 0:=by
    simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using
      (show HasFDerivAt R (fderiv ℝ R q) (q+0) from by simpa only [add_zero] using hR.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:TangentSpace 𝓘(ℝ,Model n) x)).const_add q)
  have hs:=H.comp_stationary ha (by simpa only [add_zero] using hR0)
  apply hs.congr_of_eventuallyEq
  have ht:Tendsto (fun h:TangentSpace 𝓘(ℝ,Model n) x=>q+h) (𝓝 0) (𝓝 q):=by
    have hc : ContinuousAt (fun h:TangentSpace 𝓘(ℝ,Model n) x=>q+h) 0 := continuousAt_const.add continuousAt_id
    simpa only [add_zero] using hc.tendsto
  filter_upwards [ht.eventually hRe,ht.eventually ((isOpen_injectivityDomain x).mem_nhds hq)] with h hh hhr
  dsimp only [C,normalCost]
  rw [hh,hyx]
  congr 1
  change ‖q+h‖^2/2=dist (riemannianExp x (q+h)) x^2/2
  rw [dist_comm,injectivityDomain_subset_minimizingVectors x hhr]
end NormalPoleTaylor
end WeakMTWTransport

end
end

end OAI
