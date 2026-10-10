import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose
import OAI.Analysis.BiholderTransport.Regularity.MaximumEndpoint
import OAI.Analysis.BiholderTransport.Regularity.MovingCenterUpper
import OAI.Analysis.BiholderTransport.Calculus.HopfGradientBound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterUpper
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.sample_center_upper {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {C:ℝ}
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ C*‖d‖^2) :
    ∀ᶠ k in atTop,∀d,J.sampleH k (S.ν k) d d ≤ (C+1)*‖d‖^2 := by
  filter_upwards [hL,hε.eventually (gt_mem_nhds zero_lt_one)] with k hk hεk
  intro d
  calc
    _ ≤ (J.first k).H d d+1*‖d‖^2 := bilinear_quadratic_close ((S.HClose k).le.trans hεk.le) d
    _ ≤ (J.first k).L d d+1*‖d‖^2 := by linarith only [(J.first k).upper d]
    _ ≤ C*‖d‖^2+1*‖d‖^2 := by linarith only [hk d]
    _ = _ := by ring

lemma MaximumDiagonal.center_gradient_bound {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hg:Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    ∃K≥0,∀ᶠ k in atTop,
      ‖fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))‖ ≤ K := by
  obtain ⟨K,hK,HK⟩:=exists_chart_hopf_gradient_bound (n := n) c
  have hgg:∀ᶠ k in atTop,‖J.sampleGradient k (S.ν k)‖<1 := by
    simpa only [norm_zero,Function.comp_def] using ((continuous_norm.tendsto (0:Model n →L[ℝ] ℝ)).comp hg).eventually
      (gt_mem_nhds (by simp : ‖(0:Model n →L[ℝ] ℝ)‖<1))
  refine ⟨1+K,by linarith,?_⟩
  filter_upwards [hz.eventually HK,F.time.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1)),hgg]
    with k hk htk hgk
  have houter:=hk (F.t k) htk.le (cTransform (modifiedDatum v α D (F.b k) Bo))
    (continuous_cTransform (continuous_modifiedDatum hv α D (F.b k) ho))
  let x:=(J.sample k).z (J.sampleIndex k (S.ν k))
  have he:fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) x=
      J.sampleGradient k (S.ν k)-
        fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c) x := by
    dsimp only [MaximumJensenFamily.sampleGradient,x]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hgk.le houter)

lemma MaximumDiagonal.center_upper {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C:ℝ} (hC:0 ≤ C) (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ K*‖d‖^2 := by
  obtain ⟨hb,hp,hx,hg⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨K,hK,HK⟩:=S.center_gradient_bound hg hz
  have hn:∀ᶠ k in atTop,∀ᶠ z in 𝓝 ((J.sample k).z (J.sampleIndex k (S.ν k))),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z := by
    apply Eventually.of_forall
    intro k
    filter_upwards [(J.sample k).openRegion.mem_nhds ((J.sample k).sampleInRegion (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  have hd:∀ᶠ k in atTop,DifferentiableAt ℝ
      (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) :=
    Eventually.of_forall (fun k=>((J.sample k).samples (J.sampleIndex k (S.ν k))).2.2.2.2.2.2.2.2.1)
  have HB:=S.sample_center_upper hε hL
  have H:=moving_center_sequential_upper hq he hb hp F.time
    (Gj := fun k=>hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (by simpa only [S.movingChart] using hn) (by simpa only [S.movingChart] using hd)
    hK (show 0 ≤ C+1 by linarith) (by simpa only [S.movingChart] using HK) HB
  simpa only [S.movingChart] using H

end MaximumCenterUpper
end WeakMTWTransport

end
end

end OAI
