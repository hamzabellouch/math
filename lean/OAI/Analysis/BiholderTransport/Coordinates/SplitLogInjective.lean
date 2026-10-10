import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.KernelRadial
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SplitLogInjective
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefix_log_fderiv_injective {x y : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hleft : t • p∈injectivityDomain x)
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a)) :
    Function.Injective (fderiv ℝ q p) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  apply (injective_iff_map_eq_zero (fderiv ℝ q p)).mpr
  intro v hv
  have he := (contMDiff_riemannianExp_fiber y (q p)).mdifferentiableAt (by simp)
  have hD := he.hasMFDerivAt.comp p hq.hasFDerivAt.hasMFDerivAt
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 p] (fun a : X => riemannianExp x (t • a)) := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hV : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (fun a : X => riemannianExp x (t • a)) p v=0 := by
    rw [hE]
    change mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp y) (q p) (fderiv ℝ q p v)=0
    rw [hv]
    exact map_zero _
  have hscale : HasFDerivAt (fun a : X => t • a) (t • ContinuousLinearMap.id ℝ X) p :=
    (t • ContinuousLinearMap.id ℝ X).hasFDerivAt
  have hExp := ((contMDiff_riemannianExp_fiber x (t • p)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p hscale.hasMFDerivAt
  have hEV := congrArg (fun L : X →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp x (t • p)) => L v) hExp.mfderiv
  have hW : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) (t • p) (t • v)=0 :=
    hEV.symm.trans hV
  rw [exp_mfderiv_apply_eq_coordinate] at hW
  have htv : t • v=0 := (riemannianExp_interior_nonconjugate hleft)
    (hW.trans (map_zero _).symm)
  exact (smul_eq_zero.mp htv).resolve_left ht

end SplitLogInjective
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateEndpoint (c : TangentBundle 𝓘(ℝ,Model n) M) (q : Model n×Model n) : Model n :=
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
    (riemannianExp (χ.symm q).1 (χ.symm q).2)

def coordinateEndpointVertical (c z : TangentBundle 𝓘(ℝ,Model n) M) : Model n →L[ℝ] Model n :=
  (fderiv ℝ (coordinateEndpoint c)
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z)).comp (inr ℝ (Model n) (Model n))

lemma coordinateEndpoint_contDiffAt (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hy : riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source) :
    ContDiffAt ℝ ∞ (coordinateEndpoint c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  have hχ : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm (χ z) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds (χ.map_source hz))
  have hE := contMDiff_riemannianExp.contMDiffAt.comp (χ z) hχ
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) :=
    (contMDiffOn_extChartAt (n := ∞) (x := riemannianExp c.1 c.2)).contMDiffAt
      (by simpa only [extChartAt_source] using (isOpen_extChartAt_source _).mem_nhds hy)
  have hd' : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d
      (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2) := by rwa [χ.left_inv hz]
  exact (hd'.comp (χ z) hE).contDiffAt

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma tangent_chart_fiber_inverse (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
    let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
    let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
    ∀ w, χ.symm ((χ z).1,w)=(⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
  intro χ τ L w
  have hf : χ (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M)=((χ z).1,w) := by
    apply Prod.ext
    · rfl
    · change L (L.symm w)=w
      exact L.apply_symm_apply w
  rw [←hf]
  exact χ.left_inv ((tangent_chart_source_iff c _).mpr (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz))

lemma coordinateEndpointVertical_apply (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hy : riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source)
    (v : TangentSpace 𝓘(ℝ,Model n) z.1) :
    coordinateEndpointVertical c z
      ((trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1).continuousLinearMapAt ℝ z.1 v)=
    (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)
      (riemannianExp c.1 c.2)).continuousLinearMapAt ℝ (riemannianExp z.1 z.2)
        (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2 v) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  let X := TangentSpace 𝓘(ℝ,Model n) z.1
  let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  let F : X → Model n := fun a => d (riemannianExp z.1 a)
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) :=
    (contMDiffOn_extChartAt (n := ∞) (x := riemannianExp c.1 c.2)).contMDiffAt
      (by simpa only [extChartAt_source] using (isOpen_extChartAt_source _).mem_nhds hy)
  have hF : ContDiffAt ℝ ∞ F z.2 :=
    (hd.comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hpart : (fun w => coordinateEndpoint c ((χ z).1,w))=F ∘ L.symm := by
    funext w
    dsimp only [coordinateEndpoint,F,Function.comp_apply]
    rw [tangent_chart_fiber_inverse c z hz w]
  have hG := (coordinateEndpoint_contDiffAt c z hz hy).differentiableAt (by simp)
  have hpartD := (hG.hasFDerivAt.comp (χ z).2
    ((hasFDerivAt_const (χ z).1 (χ z).2).prodMk (hasFDerivAt_id (χ z).2))).fderiv
  have hLz : (χ z).2=L z.2 := rfl
  have hFD : HasFDerivAt F (fderiv ℝ F z.2) (L.symm (χ z).2) := by
    rw [hLz,L.symm_apply_apply]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  have hRD := (hFD.comp (χ z).2 L.symm.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => coordinateEndpoint c ((χ z).1,w)) (χ z).2 =
    (fderiv ℝ (coordinateEndpoint c) (χ z)).comp (inr ℝ _ _) at hpartD
  rw [hpart] at hpartD
  have hA : coordinateEndpointVertical c z=(fderiv ℝ F z.2).comp (L.symm : Model n →L[ℝ] X) :=
    hpartD.symm.trans hRD
  have hD := (hd.mdifferentiableAt (by simp)).hasMFDerivAt.comp z.2
    ((contMDiff_riemannianExp_fiber z.1 z.2).mdifferentiableAt (by simp)).hasMFDerivAt
  have hDE : fderiv ℝ F z.2=(mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d (riemannianExp z.1 z.2)).comp
      (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2) := by
    have hm := hD.mfderiv
    rw [mfderiv_eq_fderiv] at hm
    exact hm
  have hLv : τ.continuousLinearMapAt ℝ z.1 v=L v := by
    simp only [L,Trivialization.coe_continuousLinearEquivAt_eq]
  rw [hLv]
  rw [hA,ContinuousLinearMap.comp_apply]
  change fderiv ℝ F z.2 (L.symm (L v))=_
  rw [L.symm_apply_apply,hDE]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (by simpa only [extChartAt_source] using hy)]
  rfl

end ExpCoordinates
end WeakMTWTransport

end

end

end

end OAI
