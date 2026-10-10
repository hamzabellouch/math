import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FixedJoinSpectrum
import OAI.Analysis.BiholderTransport.Coordinates.ExpVertical
import OAI.Analysis.BiholderTransport.Regularity.FrameDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpJacContinuity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance expJacContFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma frameNormDet_at {a x:M} (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a x)).toLinearMap.normDet=
      ((trivializationAt (Model n) (fun y:M=>TangentSpace 𝓘(ℝ,Model n) y) a).symmL ℝ x).toLinearMap.normDet := by
  exact congrArg (fun y:M=>((trivializationAt (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) a).symmL ℝ y).toLinearMap.normDet)
      ((extChartAt 𝓘(ℝ,Model n) a).left_inv hx)

lemma expJacobian_coordinate_identity (c z:TangentBundle 𝓘(ℝ,Model n) M)
    (hz:z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (he:riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source) :
    expJacobian z.1 z.2 *
      (chartFiberInverse c.1 (extChartAt 𝓘(ℝ,Model n) c.1 z.1)).toLinearMap.normDet=
      (chartFiberInverse (riemannianExp c.1 c.2)
        (extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2) (riemannianExp z.1 z.2))).toLinearMap.normDet*
      |(coordinateEndpointVertical c z).det| := by
  let U:=trivializationAt (Model n) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V:=trivializationAt (Model n) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  let B:=U.symmL ℝ z.1
  let C:=V.symmL ℝ (riemannianExp z.1 z.2)
  let A:=coordinateEndpointVertical c z
  let E:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp z.1 z.2):=
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2
  have hz':z.1∈(extChartAt 𝓘(ℝ,Model n) c.1).source:=(tangent_chart_source_iff _ _).mp hz
  have hU:z.1∈U.baseSet:=by simpa only [U,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hz'
  have hV:riemannianExp z.1 z.2∈V.baseSet:=by simpa only [V,TangentBundle.trivializationAt_baseSet,extChartAt_source] using he
  have hEB:E.comp B=C.comp A:=by
    apply ContinuousLinearMap.ext
    intro d
    have HH:=coordinateEndpointVertical_apply c z hz he (B d)
    rw [U.continuousLinearMapAt_symmL hU] at HH
    have HHH:=congrArg C HH
    rw [V.symmL_continuousLinearMapAt hV] at HHH
    exact HHH.symm
  rw [frameNormDet_at hz',frameNormDet_at he]
  change E.toLinearMap.normDet*B.toLinearMap.normDet=C.toLinearMap.normDet*|A.det|
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap E.toLinearMap (show Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) z.1) by rw [tangent_finrank]; exact finrank_euclideanSpace_fin)
  have h2:=LinearMap.normDet_comp_of_finrank_eq A.toLinearMap C.toLinearMap rfl
  rw [LinearMap.normDet_eq_abs_det] at h2
  change (E.comp B).toLinearMap.normDet=_ at h1
  change (C.comp A).toLinearMap.normDet=_ at h2
  rw [←h1,hEB,h2]

lemma continuous_expJacobian : Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>expJacobian z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  let e:=riemannianExp c.1 c.2
  let s:=fun z:TangentBundle 𝓘(ℝ,Model n) M=>
    (chartFiberInverse c.1 (extChartAt 𝓘(ℝ,Model n) c.1 z.1)).toLinearMap.normDet
  let t:=fun z:TangentBundle 𝓘(ℝ,Model n) M=>
    (chartFiberInverse e (extChartAt 𝓘(ℝ,Model n) e (riemannianExp z.1 z.2))).toLinearMap.normDet
  have hproj:Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>z.1):=
    (Bundle.contMDiff_proj (n:=∞) (IB:=𝓘(ℝ,Model n)) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)).continuous
  have hE:Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2):=contMDiff_riemannianExp.continuous
  have hsc:ContinuousAt (fun z:TangentBundle 𝓘(ℝ,Model n) M=>extChartAt 𝓘(ℝ,Model n) c.1 z.1) c:=
    (continuousAt_extChartAt (I:=𝓘(ℝ,Model n)) c.1).comp hproj.continuousAt
  have htc:ContinuousAt (fun z:TangentBundle 𝓘(ℝ,Model n) M=>extChartAt 𝓘(ℝ,Model n) e (riemannianExp z.1 z.2)) c:=
    (continuousAt_extChartAt (I:=𝓘(ℝ,Model n)) e).tendsto.comp hE.continuousAt
  have hs:ContinuousAt s c:= (frameNormDet_continuousAt (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c.1)).tendsto.comp hsc.tendsto
  have ht:ContinuousAt t c:= (frameNormDet_continuousAt (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) e)).tendsto.comp htc.tendsto
  have hsp:0<s c:=frameNormDet_pos (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c.1)
  have Hd:ContinuousAt (fun z=>|(coordinateEndpointVertical c z).det|) c:=
    (ContinuousLinearMap.continuous_det.continuousAt.comp (coordinateEndpointVertical_continuousAt c)).abs
  have H:ContinuousAt (fun z=>t z*|(coordinateEndpointVertical c z).det|/s z) c:=(ht.mul Hd).div hs hsp.ne'
  apply H.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I:=𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c,
    hE.continuousAt.eventually (extChartAt_source_mem_nhds (I:=𝓘(ℝ,Model n)) e),
    hs.eventually (lt_mem_nhds hsp)] with z hzs hzt hsz
  exact (eq_div_iff hsz.ne').mpr (expJacobian_coordinate_identity c z hzs hzt)
end ExpJacContinuity
end WeakMTWTransport

end
end

end OAI
