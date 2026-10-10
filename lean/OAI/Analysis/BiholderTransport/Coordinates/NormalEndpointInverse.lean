import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FixedJoinSpectrum
import OAI.Analysis.BiholderTransport.Volume.UniformJacobian
import OAI.Analysis.BiholderTransport.Convexity.EndpointLowerJet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section NormalEndpointInverse
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma exists_normal_endpoint_inverse {x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hp:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) :
    ∃ (e:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p) → TangentSpace 𝓘(ℝ,Model n) x)
      (C:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)),
      ContDiffAt ℝ ∞ e 0 ∧ e 0=p ∧
      (∀ᶠ w in 𝓝 0,riemannianExp x (e w)=riemannianExp (riemannianExp x p) w) ∧
      Function.Injective C ∧ C.comp (fderiv ℝ e 0)=ContinuousLinearMap.id ℝ _ ∧
      (fderiv ℝ e 0).comp C=ContinuousLinearMap.id ℝ _ ∧
      expJacobian x p=C.toLinearMap.normDet := by
  let y:=riemannianExp x p
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let F:=TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨e,he,he0,hei,heD⟩:=exists_smooth_normal_endpoint_log_of_nonconjugate (y:=y) rfl hp
  obtain ⟨R,hR,hR0,hRi⟩:=exists_normal_endpoint_coordinates x p
  let C:E →L[ℝ] F:=fderiv ℝ R p
  let J:F →L[ℝ] E:=fderiv ℝ e 0
  have hJD:HasFDerivAt e J 0:= (he.differentiableAt (by simp)).hasFDerivAt
  have hCD:HasFDerivAt R C p:= (hR.differentiableAt (by simp)).hasFDerivAt
  have hn:injectivityDomain y∈𝓝 (0:F):=
    (isOpen_injectivityDomain y).mem_nhds (zero_mem_injectivityDomain y)
  have hRcomp:ContinuousAt (fun w=>R (e w)) 0:=
    (show ContinuousAt R (e 0) from by rw [he0]; exact hR.continuousAt).comp he.continuousAt
  have hRcomp0:R (e 0)=0:=by rw [he0,hR0]
  have hId:(fun w:F=>R (e w)) =ᶠ[𝓝 0] id:=by
    have hrn:=hRcomp.eventually (show injectivityDomain y∈𝓝 (R (e 0)) from by rw [hRcomp0]; exact hn)
    have hri:=he.continuousAt.eventually (show ∀ᶠ v in 𝓝 (e 0),
      riemannianExp y (R v)=riemannianExp x v from by rw [he0]; exact hRi)
    filter_upwards [hei,hrn,hn,hri] with w hw hr hw0 hri
    exact riemannianExp_injOn_injectivityDomain y hr hw0 (hri.trans hw)
  have hCJ:C.comp J=ContinuousLinearMap.id ℝ F:=by
    have H:HasFDerivAt (fun w=>R (e w)) (C.comp J) 0:=
      (show HasFDerivAt R C (e 0) from by rw [he0]; exact hCD).comp 0 hJD
    exact H.fderiv.symm.trans (hId.fderiv_eq.trans (fderiv_id))
  have hsur:Function.Surjective J:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((tangent_finrank (n:=n) y).trans (tangent_finrank (n:=n) x).symm)).mp heD
  have hJC:J.comp C=ContinuousLinearMap.id ℝ E:=by
    ext d
    obtain ⟨w,rfl⟩:=hsur d
    have H:=congrArg (fun A:F →L[ℝ] F=>A w) hCJ
    change C (J w)=w at H
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,H]
  have hCI:Function.Injective C:=by
    intro d e h
    have h1:=congrArg (fun A:E →L[ℝ] E=>A d) hJC
    have h2:=congrArg (fun A:E →L[ℝ] E=>A e) hJC
    change J (C d)=d at h1
    change J (C e)=e at h2
    exact h1.symm.trans ((congrArg J h).trans h2)
  exact ⟨e,C,he,he0,hei,hCI,hCJ,hJC,
    expJacobian_eq_normal_endpoint (hR.differentiableAt (by simp)) hR0 hRi⟩
end NormalEndpointInverse
end WeakMTWTransport

end
end

end OAI
