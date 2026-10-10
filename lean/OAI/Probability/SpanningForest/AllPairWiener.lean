import OAI.Probability.SpanningForest.WienerSampler
import OAI.Probability.SpanningForest.AllPairPicardDecoder
import OAI.Probability.SpanningForest.PicardNonnegativeSampler
import OAI.Probability.SpanningForest.FactorSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.AllPairWiener
open FactorAssembly
abbrev Path := GlobalWiener.Path
local instance : MeasurableSpace Path := borel _
local instance : BorelSpace Path := ⟨rfl⟩

def law : Measure (EdgeCode → Path) :=
  Measure.infinitePi (fun _ : EdgeCode => GlobalWiener.wienerMeasure)

instance law_isProbabilityMeasure : IsProbabilityMeasure law := by
  unfold law
  infer_instance

theorem eval_hasLaw (e : EdgeCode) :
    HasLaw (fun W : EdgeCode → Path => W e) GlobalWiener.wienerMeasure law :=
  ⟨(measurable_pi_apply e).aemeasurable,
    Measure.infinitePi_map_eval (fun _ : EdgeCode => GlobalWiener.wienerMeasure) e⟩

theorem isBrownian_eval (e : EdgeCode) :
    IsBrownianReal (fun t (W : EdgeCode → Path) => W e t) law := by
  constructor
  · constructor
    intro S
    exact (GlobalWiener.isBrownian_wienerMeasure.toIsPreBrownianReal.hasLaw S).comp
      (eval_hasLaw e)
  · exact ae_of_all _ (fun W => (W e).continuous)

theorem independent_paths :
    iIndepFun (fun e (W : EdgeCode → Path) => W e) law :=
  iIndepFun_infinitePi (P := fun _ : EdgeCode => GlobalWiener.wienerMeasure)
    (X := fun _ w => w) (fun _ => measurable_id)

theorem independent_processes :
    iIndepFun (fun e (W : EdgeCode → Path) t => W e t) law :=
  iIndepFun_infinitePi (P := fun _ : EdgeCode => GlobalWiener.wienerMeasure)
    (X := fun _ (w : Path) t => w t)
    (fun _ => Measurable.of_eval (fun t => (continuous_eval_const t).measurable))

def pathEval (w : Path) (t : ℝ) : ℝ := w (Real.toNNReal t)

theorem measurable_pathEval : Measurable (Function.uncurry pathEval) :=
  ContinuousEval.continuous_eval.measurable.comp
    (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))

def paths (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : Path :=
  WienerSampler.sample (AllPairIID.uniformRule G U e)

theorem measurable_paths :
    Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) => paths q.1 q.2.1 q.2.2) :=
  WienerSampler.measurable_sample.comp AllPairIID.measurable_uniformRule_uncurried

theorem measurable_paths_field (G : GraphCode) : Measurable (paths G) := by
  apply Measurable.of_eval
  intro e
  exact WienerSampler.measurable_sample.comp (AllPairIID.measurable_uniformRule_fixed G e)

theorem paths_equivariant (σ : Equiv ℕ ℕ) (G : GraphCode)
    (U : ℕ → ℝ) (e : EdgeCode) :
    paths (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = paths G U e :=
  congrArg WienerSampler.sample (AllPairIID.uniformRule_equivariant σ G U e)

theorem paths_hasLaw {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    HasLaw (fun ω => paths G (fun v => U v ω)) law P := by
  refine ⟨((measurable_paths_field G).comp (Measurable.of_eval hU.1)).aemeasurable, ?_⟩
  exact AllPairIID.sampled_uniformRule_law GlobalWiener.wienerMeasure
    WienerSampler.sample WienerSampler.measurable_sample WienerSampler.map_sample
    G hc hf P U hU

def noise : GraphNoise := fun G U e => pathEval (paths G U e)

theorem noise_borel : NoiseBorel noise := by
  intro e
  have hp : Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ => paths p.1.1 p.1.2 e) :=
    measurable_paths.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_const))
  exact measurable_pathEval.comp (hp.prodMk measurable_snd)

theorem noise_equivariant : NoiseEquivariant noise := by
  intro σ G U e t
  exact congrArg (fun w => pathEval w t) (paths_equivariant σ G U e)

theorem continuous_noise (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) :
    Continuous (noise G U e) :=
  (paths G U e).continuous.comp continuous_real_toNNReal

theorem decoder_eq_nonnegative_sample (b : GraphDrift) (G : GraphCode) :
    AllPairPicardDecoder.decoder pathEval b G =
      PicardSampler.NonnegativeTime.sample
        (fun (W : EdgeCode → Path) e t => W e t) (b G) := by
  funext W e
  exact (PicardSampler.sample_apply_unshifted
    (fun (W : EdgeCode → Path) e => pathEval (W e)) (b G) W e).symm

theorem sampler_hasLaw_of_product
    (b : GraphDrift) (G : GraphCode) (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {ν : Measure EdgeConfiguration}
    (hLaw : HasLaw (PicardSampler.NonnegativeTime.sample
      (fun (W : EdgeCode → Path) e t => W e t) (b G)) ν law) :
    HasLaw (PicardSampler.sample (noise G) (b G)) ν privatePoolLaw := by
  exact hLaw.comp (paths_hasLaw G hc hf privatePoolLaw
    (fun v U => U v) CanonicalIID.canonical_isVertexIID)

theorem exists_factor_of_sampler_laws
    (b : GraphDrift) (hb : DriftBorel b) (heq : DriftEquivariant b)
    (ν : GraphCode → Measure EdgeConfiguration)
    (hν : ∀ G, GraphConnected G → GraphLocallyFinite G → HasFUSFLaw G (ν G) id)
    (hLaw : ∀ G, GraphConnected G → GraphLocallyFinite G →
      HasLaw (PicardSampler.NonnegativeTime.sample
        (fun (W : EdgeCode → Path) e t => W e t) (b G)) (ν G) law) :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G :=
  FactorAssembly.exists_factor_of_canonical_sampler_laws b noise hb noise_borel
    heq noise_equivariant ν hν
    (fun G hc hf => sampler_hasLaw_of_product b G hc hf (hLaw G hc hf))

end Problem336.AllPairWiener

end

end OAI
