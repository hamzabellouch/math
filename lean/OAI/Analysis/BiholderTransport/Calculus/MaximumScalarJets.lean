import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamily
import OAI.Analysis.BiholderTransport.Regularity.MaximumGoodCenters
import OAI.Analysis.BiholderTransport.Convexity.JensenUndoShort
import OAI.Analysis.BiholderTransport.Convexity.JensenPhaseGradient

namespace OAI


noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance maximumScalarDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumScalarDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumScalarBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumScalarBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma MaximumDiagonal.scalar_jets
    {u v:M → ℝ} (hu:Continuous u) {Lv:ℝ≥0} (hv:LipschitzWith Lv v)
    (hdual:IsCostDualPair u v) {α D bminus bplus A₀ B₀:ℝ} {Bc Bo:ℝ → ℝ}
    {ho:Continuous Bo} (hBc:ContDiff ℝ ∞ Bc)
    (hmono:∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (hrange:∀y,v y∈Icc A₀ B₀)
    (hslope:∀b∈Icc bminus bplus,∀y:M,
      0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1)
    {hmtw:WeakMTW (n:=n) (M:=M)}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
    {J:MaximumJensenFamily hmtw hv.continuous ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {Q:M → Prop} {r:ℝ} (hr:0<r)
    (hgood:∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r,z∉N →
      Q ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hg:Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∧
        (∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
          v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  let i:=fun k=>J.sampleIndex k (S.ν k)
  let φ:=fun k s=>modifiedScalar α D Bc (F.b k,s)
  have hφ (k:ℕ):ContDiff ℝ ∞ (φ k):=
    (modifiedScalar_contDiff hBc α D).comp (contDiff_const.prodMk contDiff_id)
  have hsl (k:ℕ) (y:M):0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1:=
    hslope _ (Ioo_subset_Icc_self (F.parameter k)) y
  have hHn : Tendsto (fun k => ‖fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))‖) atTop (𝓝 ‖H‖) := hH.norm
  have HG:∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (i k)) d d≤(‖H‖+1)*‖d‖^2:=by
    filter_upwards [hHn.eventually (gt_mem_nhds (show ‖H‖<‖H‖+1 by linarith))] with k hk
    intro d
    exact (le_abs_self _).trans ((bilinear_quadratic_norm_bound _ d).trans
      (mul_le_mul_of_nonneg_right hk.le (sq_nonneg _)))
  have Hgood:=S.good_centers hBc.continuous hx hz HG
  have HE:∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (i k))) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v (χ.symm (J.sampleCenter k (S.ν k)+h))) p A:=by
    filter_upwards [Hgood,hx.eventually (ball_mem_nhds _ hr)] with k hk hb
    have HH:=hgood _ hb hk
    have hY:χ.symm (J.sampleCenter k (S.ν k))=(J.sample k).Y ((J.sample k).z (i k)):=
      χ.left_inv ((J.sample k).samples (i k)).1
    rw [hY] at HH
    exact HH
  obtain ⟨K,hK,R,hR,hRT,Hsem⟩:=uniform_family_chart_semiconvex (n:=n)
    (modifiedScalar_contDiff hBc α D) isCompact_Icc hmono A₀ B₀ c
  have HB:∀y,cTransform u y∈Icc A₀ B₀:=by rwa [←hdual.2]
  have HS:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
      ConvexOn ℝ (ball (J.sampleCenter k (S.ν k)) r)
      (fun q=>φ k (v (χ.symm q))+K/2*‖q‖^2):=by
    filter_upwards [hx.eventually (ball_mem_nhds _ (half_pos hR))] with k hk
    have hs:=Hsem (F.b k) (Ioo_subset_Icc_self (F.parameter k)) u hu HB
    rw [←hdual.2] at hs
    refine ⟨R/2,half_pos hR,K,hs.subset ?_ (convex_ball _ _)⟩
    intro z hz'
    change dist z (χ c)<R
    calc
      dist z (χ c) ≤ dist z (J.sampleCenter k (S.ν k))+dist (J.sampleCenter k (S.ν k)) (χ c):=dist_triangle _ _ _
      _ < R/2+R/2:=add_lt_add hz' hk
      _ = R:=by ring
  obtain ⟨p,A,HPA,HA,_⟩:=hmtw.jensen_undo_short hu hv hdual hφ hsl
    (fun k=>(F.prefixTime k).1) (fun k=>(F.prefixTime k).2) J.sample i F.time hz hg hH
    (HE.mono (fun k hk=>hk.2)) HS
  have hgrad:∀ᶠ k in atTop,(coordinatePhaseFlow c (1-F.t k,(J.sample k).z (i k),
      fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (F.t k) c) ((J.sample k).z (i k)))).2=
      innerSL ℝ (p k):=by
    filter_upwards [HS,HPA] with k Hs Hp
    obtain ⟨r,hr,K,Hs⟩:=Hs
    exact hmtw.jensen_phase_gradient hu hv hdual (hφ k) (hsl k)
      (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (i k)
      (S.chart k) hr Hp.1 Hp.2 Hs
  exact ⟨p,A,(HE.and HPA).mono (fun k hk=>⟨hk.1.1,hk.2⟩),
    phase_gradient_tendsto F.time hz hg hgrad,HA⟩
end WeakMTWTransport

end

end OAI
