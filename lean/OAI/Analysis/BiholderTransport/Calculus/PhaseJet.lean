import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.CotangentFlow

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section PhaseJetAlgebra
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {P:Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma limit_from_comp_near_id {Aj Hj:ℕ → E →L[ℝ] P} {Rj:ℕ → E →L[ℝ] E}
    {H:E →L[ℝ] P} (hR:Tendsto Rj atTop (𝓝 1))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,(Aj j).comp (Rj j)=Hj j) : Tendsto Aj atTop (𝓝 H) := by
  have hi:Tendsto (fun j=>Ring.inverse (Rj j)) atTop (𝓝 (1:E →L[ℝ] E)) := by
    simpa only [Function.comp_def, Units.val_one, Ring.inverse_one] using (NormedRing.inverse_continuousAt (1:(E →L[ℝ] E)ˣ)).tendsto.comp hR
  have hu:∀ᶠ j in atTop,IsUnit (Rj j) := hR.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hl:= (ContinuousLinearMap.compL ℝ E E P).continuous₂.tendsto (H,1) |>.comp (hH.prodMk_nhds hi)
  change Tendsto (fun j=>(Hj j).comp (Ring.inverse (Rj j))) atTop (𝓝 H) at hl
  apply hl.congr'
  filter_upwards [he,hu] with j hej huj
  ext v
  have hh:=congrArg (fun T:E →L[ℝ] P=>T (Ring.inverse (Rj j) v)) hej
  have hr:Rj j (Ring.inverse (Rj j) v)=v :=
    congrArg (fun T:E →L[ℝ] E=>T v) (Ring.mul_inverse_cancel (Rj j) huj)
  simpa only [ContinuousLinearMap.comp_apply,hr] using hh.symm

lemma phase_graph_derivative_limit
    {Dj:ℕ → (E×P) →L[ℝ] (E×P)} {Hj Aj:ℕ → E →L[ℝ] P}
    {Rj:ℕ → E →L[ℝ] E} {H:E →L[ℝ] P}
    (hD:Tendsto Dj atTop (𝓝 (ContinuousLinearMap.id ℝ (E×P))))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,(Dj j).comp ((ContinuousLinearMap.id ℝ E).prod (Hj j))=
      (Rj j).prod ((Aj j).comp (Rj j))) :
    Tendsto Rj atTop (𝓝 1) ∧ Tendsto Aj atTop (𝓝 H) := by
  have hpair:Tendsto (fun j=>(ContinuousLinearMap.id ℝ E).prod (Hj j)) atTop
      (𝓝 ((ContinuousLinearMap.id ℝ E).prod H)) := (ContinuousLinearMap.prodₗᵢ ℝ).continuous.tendsto _ |>.comp (tendsto_const_nhds.prodMk_nhds hH)
  have hd:= (ContinuousLinearMap.compL ℝ E (E×P) (E×P)).continuous₂.tendsto _ |>.comp (hD.prodMk_nhds hpair)
  change Tendsto (fun j=>(Dj j).comp ((ContinuousLinearMap.id ℝ E).prod (Hj j))) atTop
    (𝓝 ((ContinuousLinearMap.id ℝ (E×P)).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hd
  rw [ContinuousLinearMap.id_comp] at hd
  have hd':Tendsto (fun j=>(Rj j).prod ((Aj j).comp (Rj j))) atTop
      (𝓝 ((ContinuousLinearMap.id ℝ E).prod H)) := hd.congr' he
  have hR:= (ContinuousLinearMap.compL ℝ E (E×P) E (ContinuousLinearMap.fst ℝ E P)).continuous.tendsto _ |>.comp hd'
  have hA:= (ContinuousLinearMap.compL ℝ E (E×P) P (ContinuousLinearMap.snd ℝ E P)).continuous.tendsto _ |>.comp hd'
  change Tendsto (fun j=>(ContinuousLinearMap.fst ℝ E P).comp ((Rj j).prod ((Aj j).comp (Rj j)))) atTop
    (𝓝 ((ContinuousLinearMap.fst ℝ E P).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hR
  simp only [ContinuousLinearMap.fst_comp_prod] at hR
  change Tendsto (fun j=>(ContinuousLinearMap.snd ℝ E P).comp ((Rj j).prod ((Aj j).comp (Rj j)))) atTop
    (𝓝 ((ContinuousLinearMap.snd ℝ E P).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hA
  simp only [ContinuousLinearMap.snd_comp_prod] at hA
  exact ⟨hR,limit_from_comp_near_id hR hA (Eventually.of_forall (fun _=>rfl))⟩
end PhaseJetAlgebra

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinate_phase_jet_limit {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {τj:ℕ → ℝ} {qj:ℕ → Phase n} {Hj Aj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ}
    {Rj:ℕ → Model n →L[ℝ] Model n} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (ht:Tendsto τj atTop (𝓝 0)) (hqj:Tendsto qj atTop (𝓝 q))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,
      (fderiv ℝ (fun v=>coordinatePhaseFlow a (τj j,v)) (qj j)).comp
        ((ContinuousLinearMap.id ℝ (Model n)).prod (Hj j))=
      (Rj j).prod ((Aj j).comp (Rj j))) :
    Tendsto Rj atTop (𝓝 1) ∧ Tendsto Aj atTop (𝓝 H) := by
  have hd := (coordinatePhaseFlow_derivative_limit hq).comp (ht.prodMk_nhds hqj)
  exact phase_graph_derivative_limit hd hH he
end WeakMTWTransport

end

end OAI
