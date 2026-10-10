import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.ModelTangentJet
import OAI.Analysis.BiholderTransport.Contact.CenterSupportFamily
import OAI.Analysis.BiholderTransport.Regularity.CenterPoleLimit
import OAI.Analysis.BiholderTransport.Convexity.MovingCenterSemibound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section ActualCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure CenterSequenceData (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ)
    (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
    (F : ℕ → Model n → ℝ) where
  row : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i) (zj i) (τj i) (lj i)
  endpoint : ∀ i,movingPrefix a (tj i) (bj i) (qj i)=zj i
  derivative : ∀ᶠ i in atTop,
    (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c (zj i)),DifferentiableAt ℝ
      (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
    DifferentiableAt ℝ (fderiv ℝ
      (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
        (extChartAt 𝓘(ℝ,Model n) c (zj i))
  gradient : Tendsto (fun i=>fderiv ℝ (F i) (extChartAt 𝓘(ℝ,Model n) c (zj i))+
    fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z))
      (extChartAt 𝓘(ℝ,Model n) c (zj i))) atTop (𝓝 0)
  backward : ∀ᶠ i in atTop,coordinateBackward c (tj i,extChartAt 𝓘(ℝ,Model n) c (zj i),
    fderiv ℝ (F i) (extChartAt 𝓘(ℝ,Model n) c (zj i)))=
      (extChartAt 𝓘(ℝ,Model n) a).symm (bj i)

lemma exists_actual_center_sequential_gain :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
      ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
      Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
      deriv (fun s=>Φ (γ,s)) (v c)=l →
      ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
        (F : ℕ → Model n → ℝ),
      ∀ D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F,
      ∀ (r q : Model n),
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
      riemannianExp a q=c →
      Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
      Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
      Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
      Tendsto qj atTop (𝓝 q) → Tendsto (fun i=>(D.row i).r) atTop (𝓝 r) →
      (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
      (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
      ∀ ε : ℝ,0<ε →
      ∀ᶠ i in atTop,∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
            (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
        coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
          (bj i) (qj i) d d := by
  obtain ⟨c0,hc0,H⟩ := exists_uniform_coordinate_center_full_pullback (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 a c u v Φ γ hv hΦ hder γj lj τj tj xj bj qj zj F D r q hr hq he
    hγ hlm hτ ht hx hb hqq hrr hτpos L hLip ε hε
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
  have hregular : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a :=
    reverse_minimizer_regular (contracted_minimizer_mem_injectivityDomain hr hl hl1)
      hq hstationary.symm he
  have hsource : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [he]
    exact mem_extChartAt_source c
  have hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
      parametricShortForward c ψ ((pj i,τj i),xj i) := Eventually.of_forall (fun i=>by
    rw [hforward,movingPrefixChart,D.endpoint])
  have hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
        (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
          (movingPrefixChart a c (tj i) (bj i) (qj i)) := by
    simpa only [movingPrefixChart,D.endpoint] using D.derivative
  have Hlow := moving_center_sequential_semibound L hc hψ hregular
    (congrArg (extChartAt 𝓘(ℝ,Model n) c) he) hsource hp hx hb hqq ht hτ hτpos hLip
      hbelow htouch hz hjet hε
  have HG := hgain hl hl1 a c r q hr hregular hstationary.symm he
    (fun s=>Φ (γ,s)) (v c) hφ2 hder
  filter_upwards [Hlow] with i hi
  intro d
  exact (sub_le_sub_right (HG d) _).trans (hi d)

end ActualCenterSemibound
end WeakMTWTransport

end
end

end OAI
