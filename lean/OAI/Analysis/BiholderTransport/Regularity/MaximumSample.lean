import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensen

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

lemma MaximumRow.jensen_graph_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    let q := fun j=>e.symm (χ.symm (J.z j))
    Tendsto (fun j=>(q j).1) atTop (𝓝 R.q.1) ∧
      Tendsto (fun j=>graphBaseCoordinate a (q j).1) atTop (𝓝 (graphBaseCoordinate a R.q.1)) ∧
      Tendsto (fun j=>graphVelocityCoordinate a (q j).1) atTop (𝓝 (graphVelocityCoordinate a R.q.1)) := by
  dsimp only
  let χ := extChartAt 𝓘(ℝ,Model n) c
  let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
  let q := fun j=>e.symm (χ.symm (J.z j))
  have HC := (continuousAt_extChartAt_symm'' (χ.map_source hc)).tendsto.comp J.points
  rw [χ.left_inv hc] at HC
  have H := (e.symm.continuous.tendsto z).comp HC
  rw [R.graph_inverse hmtw hv ho ht ht1] at H
  have Hq := continuous_subtype_val.tendsto R.q |>.comp H
  let χa := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : R.q.1∈χa.source := (tangent_chart_source_iff _ _).mpr ha
  have Hchart := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp Hq
  exact ⟨Hq,Hchart.fst_nhds,Hchart.snd_nhds⟩

lemma MaximumRow.jensen_approximation {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    let q := fun j=>e.symm (χ.symm (J.z j))
    ∀ P:ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
      (hopfLax (1-t) (modifiedDatum v α D b Bc)) t q R.q,
    ∀ ε:ℝ,0<ε → ∀ W:ℕ → Prop,(∀ᶠ j in atTop,W j) →
    ∃ j:ℕ,
      (q (P.σ j)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
      J.z (P.σ j)∈χ.target ∧
      dist (graphBaseCoordinate a (q (P.σ j)).1) (graphBaseCoordinate a R.q.1)<ε ∧
      dist (graphVelocityCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a R.q.1)<ε ∧
      dist (χ (J.Y (J.z (P.σ j)))) (χ (riemannianExp R.q.1.1 R.q.1.2))<ε ∧
      ‖fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D b Bo) t c) (J.z (P.σ j))+
        fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D b Bc) t c) (J.z (P.σ j))‖<ε ∧
      ‖coordinateCenterMatrix a t (hopfLax (1-t) (modifiedDatum v α D b Bc))
        (graphBaseCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a (q (P.σ j)).1)-P.H‖<ε ∧
      ‖coordinatePoleMatrix a t (modifiedDatum v α D b Bo)
        (graphBaseCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a (q (P.σ j)).1)-P.L‖<ε ∧
      dist (P.pj j) P.pj₀<ε ∧ dist (P.w j) P.w₀<ε ∧ W j := by
  dsimp only
  intro P ε hε W hW
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
  obtain ⟨Hq,Hb,Hp⟩ := R.jensen_graph_limit hmtw hv ho ht ht1 J hc ha
  have hσ := P.strictMono.tendsto_atTop
  have Hbase := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto R.q.1
    |>.comp (Hq.comp hσ)
  have Ha := Hbase.eventually ((isOpen_extChartAt_source _).mem_nhds ha)
  have Ht := (J.points.comp hσ).eventually ((isOpen_extChartAt_target _).mem_nhds
    ((extChartAt 𝓘(ℝ,Model n) c).map_source hc))
  have HB := (Hb.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HP := (Hp.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HY := ((R.jensen_center_limit J hc).comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HG := (J.gradients.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HH := P.HLimit.eventually (Metric.ball_mem_nhds P.H hε)
  have HL := P.LLimit.eventually (Metric.ball_mem_nhds P.L hε)
  have Hi := P.pjLimit.eventually (Metric.ball_mem_nhds _ hε)
  have Hw := P.wLimit.eventually (Metric.ball_mem_nhds _ hε)
  have Hall := Ha.and (Ht.and (HB.and (HP.and (HY.and (HG.and (HH.and (HL.and (Hi.and (Hw.and hW)))))))))
  obtain ⟨j,hj⟩ := Hall.exists
  exact ⟨j,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_zero_right] using hj.2.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_eq_norm] using hj.2.2.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_eq_norm] using hj.2.2.2.2.2.2.2.1,
    hj.2.2.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2.2.2.2⟩

end WeakMTWTransport

end

end OAI
