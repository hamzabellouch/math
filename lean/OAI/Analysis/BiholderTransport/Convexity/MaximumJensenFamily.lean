import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumCompact
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensen
import OAI.Analysis.BiholderTransport.Convexity.FamilyJensen

namespace OAI


noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure MaximumJensenFamily {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c : M) (N : Set (Model n)) where
  poleSource : ∀ k,(F.row k).q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source
  endpointSource : ∀ k,F.z k∈(extChartAt 𝓘(ℝ,Model n) c).source
  sample : ∀ k,JensenSamplesAt (modifiedDatum v α D (F.b k) Bo)
    (modifiedDatum v α D (F.b k) Bc) (F.t k) c (F.z k) N
  first : ∀ k,
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
      (F.prefixTime k).1 (F.prefixTime k).2
    ChartFixedPrefixLimit a (modifiedDatum v α D (F.b k) Bo)
      (hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc)) (F.t k)
      (fun j=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm ((sample k).z j))) (F.row k).q

lemma MaximumFamily.eventually_jensen_first (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    (hΦ : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>p.2+p.1*Bc ((p.2-α)/D)))
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>s+b*Bc ((s-α)/D))) {Lφ : ℝ≥0}
    (hLip : ∀ b∈Icc bminus bplus,LipschitzWith Lφ (fun s=>s+b*Bc ((s-α)/D)))
    {A B : ℝ} (hbound : ∀ y,v y∈Icc A B)
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) {N:Set (Model n)} (hN : volume N=0) :
    ∃ K:ℕ,Nonempty (MaximumJensenFamily hmtw hv ho (F.comp (fun k=>k+K) (tendsto_add_atTop_nat K))
      Q.1 (riemannianExp Q.1 Q.2) N) := by
  let c := riemannianExp Q.1 Q.2
  let χ := extChartAt 𝓘(ℝ,Model n) c
  obtain ⟨R,hR,δ,hδ,H⟩ := hmtw.family_jensen_samples hΦ isCompact_Icc hmono hLip A B c
  have hz := F.limit_coordinates hQ |>.2.2.1
  have hχ : Tendsto (fun k=>χ (F.z k)) atTop (𝓝 (χ c)) :=
    ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hz
  have hpole := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto Q |>.comp hQ
  have htime : Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time :
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have hevent : ∀ᶠ k in atTop,(F.row k).q.1.1∈(extChartAt 𝓘(ℝ,Model n) Q.1).source ∧
      F.z k∈χ.source ∧ χ (F.z k)∈ball (χ c) R ∧ 1-F.t k<1/2 ∧ 1-F.t k<δ := by
    filter_upwards [hpole.eventually ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) Q.1)),
      hz.eventually ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c)),
      hχ.eventually (ball_mem_nhds _ hR),htime.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      htime.eventually (gt_mem_nhds hδ)] with k ha hc hb ht hd
    exact ⟨ha,hc,hb,ht,hd⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp hevent
  let F1 := F.comp (fun k=>k+K) (tendsto_add_atTop_nat K)
  have hk (k:ℕ) := hK (k+K) (Nat.le_add_left _ _)
  have HJ : ∀ k,Nonempty (JensenSamplesAt (modifiedDatum v α D (F1.b k) Bo)
      (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c (F1.z k) N) := by
    intro k
    have HB : ∀ y,cTransform u y∈Icc A B := by rwa [←hdual.2]
    have Hψ : Continuous (fun s:ℝ=>s+F1.b k*Bo ((s-α)/D)) :=
      continuous_id.add (continuous_const.mul (ho.comp ((continuous_id.sub continuous_const).div_const D)))
    have HH := H (F1.b k) (Ioo_subset_Icc_self (F1.parameter k)) u hu HB
      (fun s=>s+F1.b k*Bo ((s-α)/D)) Hψ (1-F1.t k) (by linarith [(F1.prefixTime k).2])
      (hk k).2.2.2.1 (hk k).2.2.2.2 (F1.z k) (hk k).2.2.1
    have hback : 1-(1-F1.t k)=F1.t k := by ring
    rw [hback,←hdual.2] at HH
    apply HH ?_ N hN
    have HM : ∀ w:Model n,
        chartOuterEnvelope (modifiedDatum v α D (F1.b k) Bo) (F1.t k) c w+
        chartCenterEnvelope (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c w≤
        chartOuterEnvelope (modifiedDatum v α D (F1.b k) Bo) (F1.t k) c (χ (F1.z k))+
        chartCenterEnvelope (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c (χ (F1.z k)) := by
      intro w
      have HX := F1.maximum k (F1.b k,χ.symm w) (Ioo_subset_Icc_self (F1.parameter k))
      dsimp only [regularizedComparison] at HX
      dsimp only [chartOuterEnvelope,chartCenterEnvelope]
      rw [show (extChartAt 𝓘(ℝ,Model n) c).symm (χ (F1.z k))=F1.z k from
        χ.left_inv (hk k).2.1]
      linarith only [HX]
    exact Eventually.of_forall HM
  let J := fun k=>Classical.choice (HJ k)
  let P := fun k=>Classical.choice ((F1.row k).jensen_first_limit hmtw hv ho
    (F1.prefixTime k).1 (F1.prefixTime k).2 (J k) (hk k).2.1 (hk k).1)
  exact ⟨K,⟨⟨fun k=>(hk k).1,fun k=>(hk k).2.1,J,P⟩⟩⟩

end WeakMTWTransport

end

end OAI
