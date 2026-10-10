import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterUpper
import OAI.Analysis.BiholderTransport.Regularity.MovingCenterLower

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance maximumDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma MaximumDiagonal.sample_center_lower {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {C:ℝ}
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d) :
    ∀ᶠ k in atTop,∀d,-(C+1)*‖d‖^2 ≤ J.sampleH k (S.ν k) d d := by
  filter_upwards [hH,hε.eventually (gt_mem_nhds zero_lt_one)] with k hk hεk
  intro d
  have hn : ‖(J.first k).H-J.sampleH k (S.ν k)‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact (S.HClose k).le.trans hεk.le
  have hclose:=bilinear_quadratic_close hn d
  nlinarith only [hclose,hk d]

lemma MaximumDiagonal.center_lower {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C:ℝ} (hC:0 ≤ C) (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d) :
    ∃K≥0,∀ᶠ k in atTop,∀d,-K*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d := by
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
  have HB:=S.sample_center_lower hε hH
  have H:=moving_center_sequential_lower hq he hb hp F.time
    (Gj := fun k=>hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (by simpa only [S.movingChart] using hn) (by simpa only [S.movingChart] using hd)
    hK (show 0 ≤ C+1 by linarith) (by simpa only [S.movingChart] using HK) HB
  simpa only [S.movingChart] using H

lemma MaximumDiagonal.center_compact {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C U:ℝ} (hC:0 ≤ C) (hD:0 ≤ U)
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun i=>fderiv ℝ
        (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B) := by
  obtain ⟨K,hK,HK⟩:=S.center_lower hε hq he hQ hC hH
  obtain ⟨L,hL',HL⟩:=S.center_upper hε hq he hQ hD hL
  change ∃ B σ, StrictMono σ ∧ Tendsto ((fun k => fderiv ℝ
    (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
      ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∘ σ) atTop (𝓝 B)
  apply exists_bilinear_limit (C := K+L)
  filter_upwards [HK,HL] with i hi hl
  apply symmetric_bilinear_norm_of_two_bounds (C := K) (D := L) _ hK hL' hi hl
  apply rough_hessian_symmetric
  · filter_upwards [(J.sample i).openRegion.mem_nhds
      ((J.sample i).sampleInRegion (J.sampleIndex i (S.ν i)))] with z hz
    exact (J.sample i).centerDifferentiable z hz
  · exact ((J.sample i).samples (J.sampleIndex i (S.ν i))).2.2.2.2.2.2.2.2.1

end MaximumCenterCompact
end WeakMTWTransport

end
end

end OAI
