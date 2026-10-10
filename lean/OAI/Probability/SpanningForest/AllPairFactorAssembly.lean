import OAI.Probability.SpanningForest.AllPairIID
import OAI.Probability.SpanningForest.EdgeAction
import OAI.Probability.SpanningForest.FUSFLawUnique

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336

theorem factor_witness_of_all_pair_decoder {Y : Type} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (D : GraphCode → (EdgeCode → Y) → EdgeConfiguration)
    (hD : Measurable (fun q : GraphCode × ((EdgeCode → Y) × EdgeCode) =>
      D q.1 q.2.1 q.2.2))
    (hEquiv : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (W : EdgeCode → Y) (e : EdgeCode),
      D (relabelGraph σ G) (fun f => W (mapEdge σ.symm f)) (mapEdge σ e) = D G W e)
    (hLaw : ∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
      HasFUSFLaw G (Measure.infinitePi (fun _ : EdgeCode => ν)) (D G)) :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G := by
  obtain ⟨Ψ, hΨ, hΨeq, hΨlaw⟩ := AllPairIID.exists_equivariant_all_pair_iid_sampler ν
  let Phi : FactorRule := fun G U => D G (Ψ G U)
  have hΨfield : Measurable (fun q : GraphCode × (ℕ → ℝ) => Ψ q.1 q.2) := by
    apply Measurable.of_eval
    intro e
    exact hΨ.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hPhi : RuleBorel Phi := by
    exact hD.comp (measurable_fst.prodMk
      ((hΨfield.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  refine ⟨Phi, hPhi, ?_, ?_⟩
  · intro σ G U e
    have hfield : Ψ (relabelGraph σ G) (relabelLabels σ U) =
        fun f => Ψ G U (mapEdge σ.symm f) := by
      funext f
      simpa only [mapEdge_apply_symm] using hΨeq σ G U (mapEdge σ.symm f)
    change D (relabelGraph σ G) (Ψ (relabelGraph σ G) (relabelLabels σ U))
      (mapEdge σ e) = D G (Ψ G U) e
    rw [hfield]
    exact hEquiv σ G (Ψ G U) e
  · intro G hconn hfin Ω _ P U hU
    have hlabels : Measurable (fun ω i => U i ω) := Measurable.of_eval hU.1
    have hinput : Measurable (fun ω => Ψ G (fun i => U i ω)) :=
      hΨfield.comp (measurable_const.prodMk hlabels)
    have hdecode : Measurable (D G) := by
      apply Measurable.of_eval
      intro e
      exact hD.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
    have houtput : Measurable (fun ω => Phi G (fun i => U i ω)) := hdecode.comp hinput
    have hreference := hLaw G hconn hfin
    have hinputlaw := hΨlaw G hconn hfin Ω P U hU
    have hmap : P.map (fun ω => Phi G (fun i => U i ω)) =
        (Measure.infinitePi (fun _ : EdgeCode => ν)).map (D G) := by
      change P.map ((D G) ∘ (fun ω => Ψ G (fun i => U i ω))) = _
      rw [← Measure.map_map hdecode hinput, hinputlaw]
    refine ⟨fun e => (measurable_pi_apply e).comp houtput, ?_⟩
    intro H hH A B
    have hcyl := congrArg (fun μ : Measure EdgeConfiguration =>
      μ (configurationCylinder A B)) hmap
    rw [Measure.map_apply houtput (measurableSet_configurationCylinder A B),
      Measure.map_apply hdecode (measurableSet_configurationCylinder A B)] at hcyl
    rw [show P {ω | (∀ e ∈ A, Phi G (fun i => U i ω) e = true) ∧
      (∀ e ∈ B, Phi G (fun i => U i ω) e = false)} =
      (Measure.infinitePi (fun _ : EdgeCode => ν))
        {W | (∀ e ∈ A, D G W e = true) ∧ (∀ e ∈ B, D G W e = false)} from hcyl]
    exact hreference.2 H hH A B

end Problem336

end

end OAI
