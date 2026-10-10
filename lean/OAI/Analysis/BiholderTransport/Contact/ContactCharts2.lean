import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_selection_chart_differential_full {v : M → ℝ} (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0)
    {G : Set M} (hG : ∀ z∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) z)
    {x : M} (hxG : x∈G) {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hTxs : T x∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
    ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
      HasFDerivWithinAt
        ((extChartAt 𝓘(ℝ,Model n) b) ∘ T ∘ (extChartAt 𝓘(ℝ,Model n) a).symm)
        (S.comp ((normalHessianOperator x p+A).comp R))
        ((extChartAt 𝓘(ℝ,Model n) a) '' G) ((extChartAt 𝓘(ℝ,Model n) a) x) ∧
      S=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p ∧
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
        ContinuousLinearMap.id ℝ (Model n) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let d := extChartAt 𝓘(ℝ,Model n) a
  let e := extChartAt 𝓘(ℝ,Model n) b
  have hx : x∈d.source := hGs hxG
  have hDx := hG x hxG
  have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv hDx (hT x) hp.2
  obtain ⟨r,hr,q,hq0,hqc,hqright,hq⟩ :=
    contact_selection_normal_differential hv hp hpI hDx hA hexp hT
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at (zero_mem_injectivityDomain (n := n) x)
  simp only [riemannianExp_zero] at hκ0 hκ hκright
  let η : Model n → V := κ ∘ d.symm
  let ξ : V → Model n := e ∘ riemannianExp x
  have hη0 : η (d x)=0 := by simp only [η,Function.comp_apply,d.left_inv hx,hκ0]
  have hdi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d x) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (d.map_source hx))
  have hη : ContDiffAt ℝ ∞ η (d x) := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp (d x) _ hdi
    simpa only [d.left_inv hx] using hκ
  have hξ : ContDiffAt ℝ ∞ ξ p := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp p _ (contMDiff_riemannianExp_fiber x p)
    apply contMDiffAt_extChartAt'
    simpa only [←hTx,extChartAt_source] using hTxs
  have hηt : Tendsto η (𝓝 (d x)) (𝓝 (0:V)) := by
    simpa only [ContinuousAt,hη0] using hη.continuousAt
  have hdiT : Tendsto d.symm (𝓝 (d x)) (𝓝 x) := by
    simpa only [ContinuousAt,d.left_inv hx] using hdi.continuousAt
  have hηright : ∀ᶠ z in 𝓝 (d x), riemannianExp x (η z)=d.symm z := hdiT.eventually hκright
  let s : Set V := {h | h∈Metric.ball 0 r ∧
    DifferentiableAt ℝ (fun z => cTransform v (riemannianExp x z)) h}
  have hηs : ∀ᶠ z in 𝓝[d '' G] (d x), η z∈s := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hηright,
      mem_nhdsWithin_of_mem_nhds (hηt.eventually (Metric.ball_mem_nhds 0 hr))] with z hz he hzball
    refine ⟨hzball,?_⟩
    obtain ⟨w,hw,rfl⟩ := hz
    have hew : riemannianExp x (η (d w))=w := by simpa only [d.left_inv (hGs hw)] using he
    have H := (show MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp x (η (d w))) from hew.symm ▸ hG w hw).comp (η (d w))
        ((contMDiff_riemannianExp_fiber x _).mdifferentiableAt (by simp))
    exact H.differentiableAt
  have hηwt : Tendsto η (𝓝[d '' G] (d x)) (𝓝[s] (η (d x))) := by
    rw [hη0]
    exact tendsto_nhdsWithin_iff.mpr ⟨hηt.mono_left nhdsWithin_le_nhds,hηs⟩
  let R := fderiv ℝ η (d x)
  let S := fderiv ℝ ξ p
  have hWq : HasFDerivWithinAt q (normalHessianOperator x p+A) s (η (d x)) := by
    simpa only [hη0] using hq
  have hqη := hWq.comp_of_tendsto (d x)
    (hη.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt hηwt
  have hξd : HasFDerivAt ξ S ((q ∘ η) (d x)) := by
    simpa only [Function.comp_apply,hη0,hq0] using
      (hξ.differentiableAt (by simp)).hasFDerivAt
  refine ⟨R,S,?_,rfl,?_⟩
  · apply (hξd.comp_hasFDerivWithinAt (d x) hqη).congr_of_eventuallyEq
    · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      filter_upwards [hηright,hηt.eventually hqright] with z hz hqz
      simp only [Function.comp_apply,ξ]
      rw [hqz,hz]
    · change e (T (d.symm (d x)))=ξ (q (η (d x)))
      simp only [ξ,Function.comp_apply,hη0,hq0,d.left_inv hx,hTx]
  · let χ : V → Model n := d ∘ riemannianExp (n := n) x
    have hχ : ContDiffAt ℝ ∞ χ 0 := by
      apply ContMDiffAt.contDiffAt
      apply ContMDiffAt.comp 0 _ (contMDiff_riemannianExp_fiber x 0)
      apply contMDiffAt_extChartAt'
      simpa only [riemannianExp_zero,d,extChartAt_source] using hx
    have hχd : HasFDerivAt χ (fderiv ℝ χ 0) (η (d x)) := by
      simpa only [hη0] using (hχ.differentiableAt (by simp)).hasFDerivAt
    have hprod := hχd.comp (d x) (hη.differentiableAt (by simp)).hasFDerivAt
    have hEq : (χ ∘ η)=ᶠ[𝓝 (d x)] id := by
      filter_upwards [hηright,(isOpen_extChartAt_target a).mem_nhds (d.map_source hx)] with z hz hzt
      change d (riemannianExp x (η z))=z
      rw [hz,d.right_inv hzt]
    exact (hprod.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_id (d x))

end ContactCharts
end WeakMTWTransport

end

end

end

end OAI
