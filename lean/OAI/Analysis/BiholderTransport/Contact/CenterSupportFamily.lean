import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ActualEnvelopeJets
import OAI.Analysis.BiholderTransport.Regularity.ActualCenterRay
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingCoordinateLimit

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure TrueCenterRow (c : M) (u v : M → ℝ) (φ : ℝ → ℝ)
    (x : Model n) (z : M) (τ l : ℝ) where
  r : Model n
  chart : x∈(extChartAt 𝓘(ℝ,Model n) c).target
  minimizing : chartFiberInverse c x r∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) c).symm x)
  contact : contactGap v u ((extChartAt 𝓘(ℝ,Model n) c).symm x) (movingNormal c (x,r))=0
  modifiedRegular : l • chartFiberInverse c x r∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm x)
  ray : riemannianExp ((extChartAt 𝓘(ℝ,Model n) c).symm x) ((τ*l) • chartFiberInverse c x r)=z
  below : ∀ w,coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),w)≤
      φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm w))
  touching : coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),x)=
      φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm x))
  forward : shortForward c (fun w=>coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),w)) (τ,x)=
      extChartAt 𝓘(ℝ,Model n) c z

lemma WeakMTW.actual_center_row (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ) (hmono : Monotone φ)
    {c : M} {x : Model n} (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target)
    {z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) c).symm x)))
    (hl : 0<l) (hl1 : l<1) (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun y=>φ (v y)) z=φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm x))+
      cost ((extChartAt 𝓘(ℝ,Model n) c).symm x) z/τ) :
    Nonempty (TrueCenterRow c u v φ x z τ l) := by
  obtain ⟨p,hm,hc,hr,he,hb,ht,hf⟩ := hmtw.exists_center_coordinate_support hu hv hdual hφc hmono hx hφ hl hl1 hτ hτ1 hval
  exact ⟨⟨p,hx,hm,hc,hr,he,hb,ht,hf⟩⟩

abbrev centerRowParameter (c : M) (v : M → ℝ) (γ l : ℝ) (x r : Model n) :=
  (γ,((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)))

omit [CompactSpace M] [Nonempty M]
  [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_row_parameter_tendsto {c : M} {v : M → ℝ} (hv : Continuous v)
    {γj lj : ℕ → ℝ} {xj rj : ℕ → Model n} {γ l : ℝ} {r : Model n}
    (hγ : Tendsto γj atTop (𝓝 γ)) (hl : Tendsto lj atTop (𝓝 l))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr : Tendsto rj atTop (𝓝 r)) :
    Tendsto (fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (rj i)) atTop
      (𝓝 (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hy := (continuousAt_extChartAt_symm'' hb).tendsto.comp hx
  rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)] at hy
  exact hγ.prodMk_nhds (((hv.tendsto c).comp hy).prodMk_nhds
    ((tendsto_const_nhds.add hl).div_const 2) |>.prodMk_nhds (hx.prodMk_nhds hr))

omit [Nonempty M] in
lemma center_support_family_subseq {c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj : ℕ → ℝ} {xj : ℕ → Model n} {zj : ℕ → M}
    (R : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i) (zj i) (τj i) (lj i))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      Tendsto (fun i=>(R (σ i)).r) atTop (𝓝 r) :=
  minimizing_coordinates_tail_subseq hx (fun i=>(R i).chart) (fun i=>(R i).minimizing)

omit [Nonempty M] in
lemma center_limit_support_smooth {c : M} {r : Model n} {γ l : ℝ} {v : M → ℝ}
    {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ (γ,v c))
    (hr : (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c)
    (hl : 0<l) (hl1 : l<1) :
    ContDiffAt ℝ ∞ (jointScalarSupport c Φ)
      ((γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r))),extChartAt 𝓘(ℝ,Model n) c c) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hp : ((1+l)/2) • chartFiberInverse c (extChartAt 𝓘(ℝ,Model n) c c) r∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm (extChartAt 𝓘(ℝ,Model n) c c)) := by
    rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)]
    exact contracted_minimizer_mem_injectivityDomain hr (by linarith) (by linarith)
  exact jointScalarSupport_contDiffAt hb (by linarith) hp hΦ

end WeakMTWTransport

end

end OAI
