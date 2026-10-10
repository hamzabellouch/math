import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ActualCenterSemibound

namespace OAI

section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterPoleStationary
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma CenterSequenceData.pole {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
    (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
    (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
    {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
    {F:ℕ → Model n → ℝ}
    (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    {r:Model n} (hr:(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c)
    (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
    (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
    (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hrr:Tendsto (fun i=>(D.row i).r) atTop (𝓝 r))
    (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
    (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
    a=riemannianExp c (l • r) := by
  let p := (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))
  let pj := fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (D.row i).r
  let ψ := jointScalarSupport (n := n) c Φ
  have hp : Tendsto pj atTop (𝓝 p) := center_row_parameter_tendsto hv hγ hlm hx hrr
  have hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c) :=
    center_limit_support_smooth hΦ hr hl hl1
  have hs : ((1+l)/2)≠0 := by linarith
  have hr' := contracted_minimizer_mem_injectivityDomain hr (t := (1+l)/2)
    (by linarith) (by linarith)
  have hc := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hφinf : ContDiffAt ℝ ∞ (fun s=>Φ (γ,s)) (v c) :=
    hΦ.comp (v c) (contDiffAt_const.prodMk contDiffAt_id)
  have hφ2 : ContDiffAt ℝ 2 (fun s=>Φ (γ,s)) (v c) :=
    hφinf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφ : HasDerivAt (fun s=>Φ (γ,s)) l (v c) := by
    rw [←hder]
    exact (hφinf.differentiableAt (by simp)).hasDerivAt
  have hforward (i : ℕ) : parametricShortForward c ψ ((pj i,τj i),xj i)=
      extChartAt 𝓘(ℝ,Model n) c (zj i) := (D.row i).forward
  have hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm w)) :=
    Eventually.of_forall (fun i=>(D.row i).below)
  have htouch : ∀ᶠ i in atTop,
      Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i)))=ψ (pj i,xj i) :=
    Eventually.of_forall (fun i=>(D.row i).touching.symm)
  have ha : Tendsto (fun i=>(extChartAt 𝓘(ℝ,Model n) a).symm (bj i)) atTop (𝓝 a) := by
    have hb0 := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
    have hy := (continuousAt_extChartAt_symm'' hb0).tendsto.comp hb
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)] at hy
    exact hy
  have hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)) := by
    filter_upwards [D.derivative] with i hi
    rw [hforward]
    exact hi.1.self_of_nhds
  have herr := D.gradient.congr' (Eventually.of_forall (fun i=>by rw [←hforward i]))
  have hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=
        (extChartAt 𝓘(ℝ,Model n) a).symm (bj i) := by
    simpa only [hforward] using D.backward
  have hstationary : a=riemannianExp c (l • r) :=
    parametric_short_center_pole_limit L hψ hs hr' hφ rfl hp hx ht hτ ha hτpos hLip
      hbelow htouch hd herr hback
  exact hstationary

end CenterPoleStationary
end WeakMTWTransport

end
end

end OAI
