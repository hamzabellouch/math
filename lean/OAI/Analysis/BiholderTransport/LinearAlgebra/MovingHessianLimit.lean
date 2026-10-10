import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeJetTest

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_clm_apply {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℝ] F} {v : ι → E} {A₀ : E →L[ℝ] F} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i=>A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hc : Continuous (fun q:(E →L[ℝ] F)×E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A₀,v₀)).comp (hA.prodMk_nhds hv)

lemma moving_rough_hessian_limit {ι : Type*} {l : Filter ι}
    {f : F → ℝ} {g : Q → E → F} {b : ι → Q} {x : ι → E}
    {b₀ : Q} {x₀ : E} {j : F →L[ℝ] ℝ} {H : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (b₀,x₀))
    (hb : Tendsto b l (𝓝 b₀)) (hx : Tendsto x l (𝓝 x₀))
    (hj : Tendsto (fun i=>fderiv ℝ f (g (b i) (x i))) l (𝓝 j))
    (hH : Tendsto (fun i=>fderiv ℝ (fderiv ℝ f) (g (b i) (x i))) l (𝓝 H))
    (hD : ∀ᶠ i in l,(∀ᶠ y in 𝓝 (g (b i) (x i)),DifferentiableAt ℝ f y) ∧
      DifferentiableAt ℝ (fderiv ℝ f) (g (b i) (x i))) :
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (fun q=>f (g (b i) q))) (x i)) l
      (𝓝 (secondJetPullback j H (fderiv ℝ (g b₀) x₀)
        (fderiv ℝ (fderiv ℝ (g b₀)) x₀))) := by
  have hbx := hb.prodMk_nhds hx
  have hm := ((ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto).comp hbx
  have hr := ((ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto).comp hbx
  have ht := secondJetPullback_tendsto hj hH hm hr
  apply ht.congr'
  have hg2 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  filter_upwards [hD,hbx.eventually (hg2.eventually (by norm_num))] with i hi hgi
  have hgi' : ContDiffAt ℝ 2 (g (b i)) (x i) :=
    (hgi.comp (x i) (contDiffAt_const.prodMk contDiffAt_id))
  ext d e
  exact (second_fderiv_comp_at hi.1 hi.2 hgi' d e).symm

lemma bilinear_limit_nonneg {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d:E,0≤B i d d) (d:E) :
    0≤B₀ d d := by
  exact ge_of_tendsto (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d))

lemma bilinear_limit_symm {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d e:E,B i d e=B i e d) (d e:E) :
    B₀ d e=B₀ e d := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d e))

lemma bilinear_limit_kernel {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    {v : ι → E} {v₀ : E} (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀))
    (hk : ∀ᶠ i in l,∀ d:E,B i (v i) d=0) (d:E) : B₀ v₀ d=0 := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_clm_apply (tendsto_clm_apply hB hv) tendsto_const_nhds) tendsto_const_nhds
    (hk.mono (fun i hi=>hi d))
end WeakMTWTransport

end

end OAI
