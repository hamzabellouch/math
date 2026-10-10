import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FirstMatrixLimit
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateMatrices
import OAI.Analysis.BiholderTransport.Coordinates.ChartActiveLimit

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure ChartFixedPrefixLimit (a : M) (v G : M → ℝ) (t : ℝ)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v)) where
  σ : ℕ → ℕ
  strictMono : StrictMono σ
  pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n
  w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ
  pj₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n
  w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ
  H : Model n →L[ℝ] Model n →L[ℝ] ℝ
  L : Model n →L[ℝ] Model n →L[ℝ] ℝ
  activeLimit : ∀ i,chartFiberInverse a (graphBaseCoordinate a q₀.1) (pj₀ i)∈
    activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q₀.1))
  nonnegLimit : ∀ i,0≤w₀ i
  totalLimit : ∑ i,w₀ i=1
  baryLimit : ∑ i,w₀ i • pj₀ i=graphVelocityCoordinate a q₀.1
  pjLimit : Tendsto pj atTop (𝓝 pj₀)
  wLimit : Tendsto w atTop (𝓝 w₀)
  HLimit : Tendsto (fun k=>coordinateCenterMatrix a t G
    (graphBaseCoordinate a (q (σ k)).1)
    (graphVelocityCoordinate a (q (σ k)).1)) atTop (𝓝 H)
  LLimit : Tendsto (fun k=>coordinatePoleMatrix a t v
    (graphBaseCoordinate a (q (σ k)).1)
    (graphVelocityCoordinate a (q (σ k)).1)) atTop (𝓝 L)
  positive : ∀ d:Model n,0≤L d d
  symmetric : ∀ d e:Model n,L d e=L e d
  kernel : ∀ i,∀ d:Model n,L (pj₀ i-graphVelocityCoordinate a q₀.1) d=0
  upper : ∀ d:Model n,H d d≤L d d
  samples : ∀ᶠ k in atTop,
    let b := graphBaseCoordinate a (q (σ k)).1
    let p := graphVelocityCoordinate a (q (σ k)).1
    let A := chartFiberInverse a b
    (∀ i,0≤w k i) ∧ (∑ i,w k i=1) ∧ (∑ i,w k i • pj k i=p) ∧
    (∀ i,A (pj k i)∈activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm b)) ∧
    (∀ i,0<w k i → HasLowerSecondTaylor
      (fun r:Model n=>v (movingNormal a (b,pj k i+r))+‖A (pj k i+r)‖^2/2) 0
      (w k i • coordinatePoleMatrix a t v b p))

lemma WeakMTW.first_fixed_prefix_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v G : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a c d : M}
    (ha0 : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hc : graphProjection (cTransform v) t q₀∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hd : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) d).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let F := fun z:Model n=>hopfLax t (cTransform v) (χ.symm z)
    let C := fun z:Model n=>G (χ.symm z)
    let z := fun k=>χ (graphProjection (cTransform v) t (q k))
    let z₀ := χ (graphProjection (cTransform v) t q₀)
    ∀ Af Ac : Model n →L[ℝ] Model n →L[ℝ] ℝ,
      ContinuousAt (fderiv ℝ F) z₀ → ContinuousAt (fderiv ℝ C) z₀ →
      (∀ᶠ z in 𝓝 z₀,DifferentiableAt ℝ F z ∧ DifferentiableAt ℝ C z) →
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ F) (z k)) atTop (𝓝 Af) →
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ C) (z k)) atTop (𝓝 Ac) →
      Tendsto (fun k=>fderiv ℝ F (z k)+fderiv ℝ C (z k)) atTop (𝓝 0) →
      (∀ r:Model n,Af r r+Ac r r≤0) →
      (∀ᶠ k in atTop,DifferentiableAt ℝ (fderiv ℝ F) (z k) ∧
        DifferentiableAt ℝ (fderiv ℝ C) (z k) ∧ DifferentiableAt ℝ
        (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) d
          (hopfPole (n := n) t (cTransform v) (χ.symm w))) (z k)) →
      Nonempty (ChartFixedPrefixLimit a v G t q q₀) := by
  dsimp only
  intro Af Ac hF hC hnear hAf hAc herr hquad hsample
  let χ := extChartAt 𝓘(ℝ,Model n) c
  let F := fun z:Model n=>hopfLax t (cTransform v) (χ.symm z)
  let C := fun z:Model n=>G (χ.symm z)
  let z := fun k=>χ (graphProjection (cTransform v) t (q k))
  let z₀ := χ (graphProjection (cTransform v) t q₀)
  have hzCoord : Tendsto z atTop (𝓝 z₀) :=
    ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hc)).tendsto.comp hz
  have hjF := hF.tendsto.comp hzCoord
  have hjC := hC.tendsto.comp hzCoord
  have hgrad : fderiv ℝ F z₀+fderiv ℝ C z₀=0 := tendsto_nhds_unique (hjF.add hjC) herr
  obtain ⟨K,hK,hKs,pj,w,pj₀,w₀,σ,hσ,hs,hpj,hw,ha,hn,h1,hbar⟩ :=
    hmtw.active_barycentric_tail_limit_in_chart hv ht ht1 q q₀ hz ha0
  let b := fun k=>graphBaseCoordinate a (q (σ k)).1
  let p := fun k=>graphVelocityCoordinate a (q (σ k)).1
  let b₀ := graphBaseCoordinate a q₀.1
  let p₀ := graphVelocityCoordinate a q₀.1
  have hq := hmtw.graph_points_tendsto hv ht ht1 (hz.comp hσ.tendsto_atTop)
  have hbase := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto q₀.1 |>.comp hq
  have hbsource : ∀ᶠ k in atTop,(q (σ k)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source :=
    hbase.eventually ((isOpen_extChartAt_source _).mem_nhds ha0)
  have hdsource : ∀ᶠ k in atTop,(q (σ k)).1.1∈(extChartAt 𝓘(ℝ,Model n) d).source :=
    hbase.eventually ((isOpen_extChartAt_source _).mem_nhds hd)
  have hzsource : ∀ᶠ k in atTop,graphProjection (cTransform v) t (q (σ k))∈χ.source :=
    (hz.comp hσ.tendsto_atTop).eventually ((isOpen_extChartAt_source _).mem_nhds hc)
  obtain ⟨hb,hp⟩ := hmtw.graph_coordinate_limit_in_chart hv ht ht1 (hz.comp hσ.tendsto_atTop) ha0
  have hb₀ : b₀∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source ha0
  have hp₀ : t • chartFiberInverse a b₀ p₀∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b₀) := by
    exact
      hmtw.graphCoordinate_prefix_regular hv ht ht1 q₀ ha0
  have he₀ : movingPrefix a t b₀ p₀=graphProjection (cTransform v) t q₀ := by
    exact
      movingPrefix_graph_coordinates ha0 t (q := q₀.1)
  have hg := movingPrefixChart_contDiffAt hb₀ (he₀ ▸ hc)
  have henergy := movingPrefixEnergy_contDiffAt hb₀ hp₀
  have he : ∀ᶠ k in atTop,movingPrefix a t (b k) (p k)=
      graphProjection (cTransform v) t (q (σ k)) :=
    hbsource.mono (fun k hk=>movingPrefix_graph_coordinates hk t)
  have hzEq : ∀ᶠ k in atTop,movingPrefixChart a c t (b k) (p k)=z (σ k) :=
    he.mono (fun k hk=>congrArg χ hk)
  have hM : ∀ᶠ k in atTop,
      (∀ r:Model n,0≤coordinatePoleMatrix a t v (b k) (p k) r r) ∧
      (∀ r s:Model n,coordinatePoleMatrix a t v (b k) (p k) r s=
        coordinatePoleMatrix a t v (b k) (p k) s r) ∧
      (∀ i,∀ r:Model n,coordinatePoleMatrix a t v (b k) (p k) (pj k i-p k) r=0) ∧
      (∀ i,chartFiberInverse a (b k) (pj k i)∈
        activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))) ∧
      (∀ i,0<w k i → HasLowerSecondTaylor
        (fun r:Model n=>v (movingNormal a (b k,pj k i+r))+
          ‖chartFiberInverse a (b k) (pj k i+r)‖^2/2) 0
        (w k i • coordinatePoleMatrix a t v (b k) (p k))) := by
    filter_upwards [hbsource,hdsource,hzsource,he,hzEq,hσ.tendsto_atTop.eventually hsample]
      with k hbk hdk hzk hek hzEk hsk
    have hbtk := (extChartAt 𝓘(ℝ,Model n) a).map_source hbk
    have hba : (extChartAt 𝓘(ℝ,Model n) a).symm (b k)=(q (σ k)).1.1 :=
      (extChartAt 𝓘(ℝ,Model n) a).left_inv hbk
    have hact : ∀ i,chartFiberInverse a (b k) (pj k i)∈
        activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)) :=
      fun i=>(mem_active_coordinates hKs ((hs k).1 i)).2.1
    obtain ⟨hpos,hsym,hker,hjet⟩ := hmtw.coordinate_sample_pole_matrix hv ht ht1 hbtk
      (graphCoordinate_normalSubdifferential (q (σ k)) hbk) (hek ▸ hzk) (hba ▸ hdk)
      (show DifferentiableAt ℝ _ (movingPrefixChart a c t (b k) (p k)) from hzEk ▸ hsk.2.2)
    exact ⟨hpos,hsym,fun i=>hker (pj k i) (hact i),hact,
      fun i hi=>hjet _ (pj k) (w k) (hs k).2.1 (hs k).2.2.1 (hs k).2.2.2 hact i hi⟩
  have hL_eq : ∀ᶠ k in atTop,coordinatePoleMatrix a t v (b k) (p k)=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k) := by
    filter_upwards [hbsource,hzsource,he] with k hbk hzk hek
    exact coordinatePoleMatrix_chart ((extChartAt 𝓘(ℝ,Model n) a).map_source hbk) (hek ▸ hzk)
  have hH_eq : ∀ᶠ k in atTop,coordinateCenterMatrix a t G (b k) (p k)=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)+
      fderiv ℝ (fderiv ℝ (fun r=>C (movingPrefixChart a c t (b k) r))) (p k) := by
    filter_upwards [hbsource,hzsource,he] with k hbk hzk hek
    exact coordinateCenterMatrix_chart ((extChartAt 𝓘(ℝ,Model n) a).map_source hbk) (hek ▸ hzk)
  have hDz : ∀ᶠ k in atTop,
      (∀ᶠ y in 𝓝 (movingPrefixChart a c t (b k) (p k)),DifferentiableAt ℝ F y ∧ DifferentiableAt ℝ C y) ∧
      DifferentiableAt ℝ (fderiv ℝ F) (movingPrefixChart a c t (b k) (p k)) ∧
      DifferentiableAt ℝ (fderiv ℝ C) (movingPrefixChart a c t (b k) (p k)) := by
    filter_upwards [(hzCoord.comp hσ.tendsto_atTop).eventually (eventually_eventually_nhds.mpr hnear),
      hσ.tendsto_atTop.eventually hsample,hzEq] with k hnk hsk hek
    rw [hek]
    exact ⟨hnk,hsk.1,hsk.2.1⟩
  have hpos : ∀ᶠ k in atTop,∀ r:Model n,
      0≤(fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k)) r r := by
    filter_upwards [hM,hL_eq] with k hk he; rw [←he]; exact hk.1
  have hker : ∀ᶠ k in atTop,∀ i,∀ r:Model n,
      (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k)) (pj k i-p k) r=0 := by
    filter_upwards [hM,hL_eq] with k hk he; rw [←he]; exact hk.2.2.1
  obtain ⟨H,L,hH,hL,hpositive,hkernel,hupper⟩ := first_fixed_prefix_matrix_limit
    henergy hg hb hp (fun i=>tendsto_pi_nhds.mp hpj i)
    ((hjF.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ F) hk.symm)))
    ((hjC.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ C) hk.symm)))
    ((hAf.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ (fderiv ℝ F)) hk.symm)))
    ((hAc.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ (fderiv ℝ C)) hk.symm)))
    (hDz.mono (fun k hk=>⟨hk.1.mono (fun y hy=>hy.1),hk.2.1⟩))
    (hDz.mono (fun k hk=>⟨hk.1.mono (fun y hy=>hy.2),hk.2.2⟩)) hgrad hquad hpos hker
  have hH' := hH.congr' (hH_eq.mono (fun k hk=>hk.symm))
  have hL' := hL.congr' (hL_eq.mono (fun k hk=>hk.symm))
  refine ⟨⟨σ,hσ,pj,w,pj₀,w₀,H,L,(fun i=>(mem_active_coordinates hKs (ha i)).2.1),hn,h1,hbar,hpj,hw,hH',hL',hpositive,
    fun r s=>bilinear_limit_symm hL' (hM.mono (fun k hk=>hk.2.1)) r s,?_,hupper,?_⟩⟩
  · exact hkernel
  · filter_upwards [hM] with k hk
    exact ⟨(hs k).2.1,(hs k).2.2.1,(hs k).2.2.2,hk.2.2.2.1,hk.2.2.2.2⟩

end WeakMTWTransport

end

end OAI
