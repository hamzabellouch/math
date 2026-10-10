import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeJetTest

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section MovingFamilyHessian
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma moving_family_rough_hessian_limit {ι : Type*} {l : Filter ι}
    {f : ι → F → ℝ} {g : Q → E → F} {b : ι → Q} {x : ι → E}
    {b₀ : Q} {x₀ : E} {j : F →L[ℝ] ℝ} {H : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (b₀,x₀))
    (hb : Tendsto b l (𝓝 b₀)) (hx : Tendsto x l (𝓝 x₀))
    (hj : Tendsto (fun i=>fderiv ℝ (f i) (g (b i) (x i))) l (𝓝 j))
    (hH : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (f i)) (g (b i) (x i))) l (𝓝 H))
    (hD : ∀ᶠ i in l,(∀ᶠ y in 𝓝 (g (b i) (x i)),DifferentiableAt ℝ (f i) y) ∧
      DifferentiableAt ℝ (fderiv ℝ (f i)) (g (b i) (x i))) :
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (fun q=>f i (g (b i) q))) (x i)) l
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

end MovingFamilyHessian
end WeakMTWTransport

end
end

end OAI
