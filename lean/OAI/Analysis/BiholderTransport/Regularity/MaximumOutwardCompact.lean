import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterRayLimit
import OAI.Analysis.BiholderTransport.Regularity.MaximumActiveCompact
import OAI.Analysis.BiholderTransport.Regularity.FrameOutwardLimit

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumOutwardCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.active_outward_compact
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} {β μ ν κ eta U:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (hμ:0 < μ) (hν:0 < ν) (hκ:0 < κ) (hD:0 < D)
    (hsel:∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let A:=chartFiberInverse a b
      let P:=A (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        (A ((J.first k).pj₀ i)))-α)/D
      ∃i:Fin (Module.finrank ℝ (Model n)+1),
      ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ κ*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        A ((J.first k).pj₀ i)=P+d • e ∧ μ ≤ (J.first k).w₀ i ∧
        ν*D/(inner ℝ P e) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧ Bo (si i) ≤ U) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
      ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
      ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
      ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
        Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
        Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
        (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
          activeLogs (modifiedDatum v α D β Bo) a) ∧
        (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧ μ ≤ m i₀ ∧
        (∀ᶠ k in atTop,μ ≤ (J.first (σ k)).w₀ i₀) ∧
        -2*eta ≤ (v (riemannianExp a (r i₀))-α)/D ∧
        (v (riemannianExp a (r i₀))-α)/D ≤ 1-eta ∧
        Bo ((v (riemannianExp a (r i₀))-α)/D) ≤ U ∧
        ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
          (show TangentSpace 𝓘(ℝ,Model n) a from r i₀)=
            (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
          0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
          κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
          ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m i₀*d ∧
          d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
          ‖show TangentSpace 𝓘(ℝ,Model n) a from r i₀‖^2-
            ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D := by
  classical
  let b:=fun k=>graphBaseCoordinate a (F.row k).q.1
  let p:=fun k=>graphVelocityCoordinate a (F.row k).q.1
  let S:=fun k (i:Fin (Module.finrank ℝ (Model n)+1))=>
    ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)),∃d:ℝ,
      ‖e‖=1 ∧ 0 < inner ℝ (chartFiberInverse a (b k) (p k)) e ∧
      κ*D ≤ (inner ℝ (chartFiberInverse a (b k) (p k)) e)^2 ∧ 0 < d ∧
      chartFiberInverse a (b k) ((J.first k).pj₀ i)=
        chartFiberInverse a (b k) (p k)+d • e ∧ μ ≤ (J.first k).w₀ i ∧
      ν*D/(inner ℝ (chartFiberInverse a (b k) (p k)) e) ≤ (J.first k).w₀ i*d ∧
      d ≤ 3*D/(2*(inner ℝ (chartFiberInverse a (b k) (p k)) e)) ∧
      -2*eta ≤ (v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D ∧
      (v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D < 1-eta ∧
      Bo ((v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D) ≤ U
  let i:=fun k=>if h:∃j,S k j then Classical.choose h else 0
  have Hi:∀ᶠ k in atTop,S k (i k):=by
    filter_upwards [hsel] with k hk
    change ∃j,S k j at hk
    dsimp only [i]
    rw [dite_eq_left hk]
    exact Classical.choose_spec hk
  obtain ⟨σ,hσ,r,m,i₀,hr,hm,hfix,hact,hmn,hmt,hbar⟩:=J.active_subseq hb hQ i
  have Hs:∀ᶠ k in atTop,S (σ k) i₀:=by
    filter_upwards [hσ.tendsto_atTop.eventually Hi,hfix] with k hk hki
    rwa [hki] at hk
  obtain ⟨hbase,hvel,_,_⟩:=F.limit_coordinates hQ
  have hbs:=hbase.comp hσ.tendsto_atTop
  have hps:=hvel.comp hσ.tendsto_atTop
  have hrs:=tendsto_pi_nhds.mp hr i₀
  have hms:=tendsto_pi_nhds.mp hm i₀
  have hdir:=moving_frame_outward_limit hbs hps hrs hms hμ hκ hD hν
  have HD:μ ≤ m i₀ ∧ _:=hdir (by
    filter_upwards [Hs] with k hk
    obtain ⟨e,d,he,hep,hq,hd,hrd,hm',hmom,hdb,_,_,_⟩:=hk
    exact ⟨e,d,he,hep,hq,hd,hrd,hm',hmom,hdb⟩)
  have hT: Tendsto (fun k=>(v (riemannianExp
      ((extChartAt 𝓘(ℝ,Model n) a).symm (b (σ k)))
      (chartFiberInverse a (b (σ k)) ((J.first (σ k)).pj₀ i₀)))-α)/D)
      atTop (𝓝 ((v (riemannianExp a (r i₀))-α)/D)):=by
    have he:=contMDiff_riemannianExp.continuous.continuousAt.tendsto.comp (chartRay_tendsto hbs hrs)
    exact ((hv.continuousAt.tendsto.comp he).sub tendsto_const_nhds).div_const D
  refine ⟨σ,hσ,r,m,i₀,hr,hm,hact,hmn,hmt,hbar,HD.1,?_,?_,?_,?_,HD.2⟩
  · exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,hh,_⟩:=hk; exact hh)
  · apply ge_of_tendsto hT
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,hh,_⟩:=hk; exact hh)
  · apply le_of_tendsto hT
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,_,hh,_⟩:=hk; exact hh.le)
  · apply le_of_tendsto (ho.continuousAt.tendsto.comp hT)
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,_,_,hh⟩:=hk; exact hh)

end MaximumOutwardCompact
end WeakMTWTransport

end
end

end OAI
