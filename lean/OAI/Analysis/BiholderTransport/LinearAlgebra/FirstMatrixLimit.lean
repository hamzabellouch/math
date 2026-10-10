import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingHessianLimit

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma secondJetPullback_sum_nonpos
    {j k : F →L[ℝ] ℝ} {A B : F →L[ℝ] F →L[ℝ] ℝ}
    {m : E →L[ℝ] F} {r : E →L[ℝ] E →L[ℝ] F}
    (hj : j+k=0) (hAB : ∀ d:F,A d d+B d d≤0) (e:E) :
    secondJetPullback j A m r e e+secondJetPullback k B m r e e≤0 := by
  have hs := congrArg (fun L:F →L[ℝ] ℝ=>L (r e e)) hj
  simp only [add_apply,zero_apply] at hs
  simp only [secondJetPullback_apply]
  linarith only [hs,hAB (m e)]

lemma first_fixed_prefix_matrix_limit {ι : Type*}
    {W : Q → E → ℝ} {g : Q → E → F} {f h : F → ℝ}
    {b : ℕ → Q} {p : ℕ → E} {b₀ : Q} {p₀ : E}
    {v : ℕ → ι → E} {v₀ : ι → E}
    {jf jh : F →L[ℝ] ℝ} {Af Ah : F →L[ℝ] F →L[ℝ] ℝ}
    (hW : ContDiffAt ℝ ∞ (Function.uncurry W) (b₀,p₀))
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (b₀,p₀))
    (hb : Tendsto b atTop (𝓝 b₀)) (hp : Tendsto p atTop (𝓝 p₀))
    (hv : ∀ i,Tendsto (fun k=>v k i) atTop (𝓝 (v₀ i)))
    (hjf : Tendsto (fun k=>fderiv ℝ f (g (b k) (p k))) atTop (𝓝 jf))
    (hjh : Tendsto (fun k=>fderiv ℝ h (g (b k) (p k))) atTop (𝓝 jh))
    (hAf : Tendsto (fun k=>fderiv ℝ (fderiv ℝ f) (g (b k) (p k))) atTop (𝓝 Af))
    (hAh : Tendsto (fun k=>fderiv ℝ (fderiv ℝ h) (g (b k) (p k))) atTop (𝓝 Ah))
    (hDf : ∀ᶠ k in atTop,(∀ᶠ y in 𝓝 (g (b k) (p k)),DifferentiableAt ℝ f y) ∧
      DifferentiableAt ℝ (fderiv ℝ f) (g (b k) (p k)))
    (hDh : ∀ᶠ k in atTop,(∀ᶠ y in 𝓝 (g (b k) (p k)),DifferentiableAt ℝ h y) ∧
      DifferentiableAt ℝ (fderiv ℝ h) (g (b k) (p k)))
    (hgrad : jf+jh=0) (hquad : ∀ d:F,Af d d+Ah d d≤0)
    (hpos : ∀ᶠ k in atTop,∀ d:E,
      0≤(fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) d d)
    (hker : ∀ᶠ k in atTop,∀ i:ι,∀ d:E,
      (fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) (v k i-p k) d=0) :
    ∃ H L : E →L[ℝ] E →L[ℝ] ℝ,
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)+
        fderiv ℝ (fderiv ℝ (fun q=>h (g (b k) q))) (p k)) atTop (𝓝 H) ∧
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) atTop (𝓝 L) ∧
      (∀ d:E,0≤L d d) ∧ (∀ i:ι,∀ d:E,L (v₀ i-p₀) d=0) ∧
      (∀ d:E,H d d≤L d d) := by
  let T := fderiv ℝ (fderiv ℝ (W b₀)) p₀
  let m := fderiv ℝ (g b₀) p₀
  let r := fderiv ℝ (fderiv ℝ (g b₀)) p₀
  let F₀ := secondJetPullback jf Af m r
  let G₀ := secondJetPullback jh Ah m r
  have hT : Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)) atTop (𝓝 T) :=
    ((ContDiffAt.partial_snd_fderiv_two hW).continuousAt.tendsto).comp (hb.prodMk_nhds hp)
  have hF := moving_rough_hessian_limit hg hb hp hjf hAf hDf
  have hG := moving_rough_hessian_limit hg hb hp hjh hAh hDh
  have hH := hT.add hG
  have hL := hT.sub hF
  refine ⟨T+G₀,T-F₀,hH,hL,fun d=>bilinear_limit_nonneg hL hpos d,?_,?_⟩
  · intro i d
    exact bilinear_limit_kernel hL ((hv i).sub hp) (hker.mono (fun k hk=>hk i)) d
  · intro d
    have H := secondJetPullback_sum_nonpos (m := m) (r := r) hgrad hquad d
    change T d d+G₀ d d≤T d d-F₀ d d
    linarith only [H]

end WeakMTWTransport

end

end OAI
