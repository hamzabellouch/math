import OAI.Probability.SpanningForest.AllPairAllocation
import OAI.Probability.SpanningForest.EdgeUniformRule

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem336.AllPairIID

local instance : IsProbabilityMeasure uniform01 := sampler_uniform01_probability
local instance : IsProbabilityMeasure privatePoolLaw := privatePoolLaw_probability
local instance : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

def raw (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ :=
  EdgeIID.pool U (AllPairAllocation.coordinateNat G (EdgeIID.keys U) e)

theorem measurable_coordinate_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun key => AllPairAllocation.coordinateNat G key e) :=
  AllPairAllocation.measurable_coordinateNat.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem measurable_raw_joint :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => raw q.1.1 q.1.2 q.2) := by
  have hk := EdgeIID.measurable_keys.comp
    (measurable_fst.snd : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => q.1.2))
  have hp := EdgeIID.measurable_pool.comp
    (measurable_fst.snd : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode => q.1.2))
  have ha := AllPairAllocation.measurable_coordinateNat.comp
    ((measurable_fst.fst.prodMk hk).prodMk measurable_snd)
  have he : Measurable (fun p : ((ℕ × ℕ) → ℝ) × (ℕ × ℕ) => p.1 p.2) :=
    measurable_from_prod_countable_left fun p => measurable_pi_apply p
  exact he.comp (hp.prodMk ha)

theorem measurable_raw (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => raw G U e) :=
  measurable_raw_joint.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem map_keys_raw (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (fun U => (EdgeIID.keys U, raw G U)) =
      privatePoolLaw.prod (Measure.infinitePi (fun _ : EdgeCode => uniform01)) := by
  apply RandomReindex.map_random_injective_reindex_of_joint_law
    privatePoolLaw privatePoolLaw uniform01 EdgeIID.keys EdgeIID.pool
    EdgeIID.measurable_keys EdgeIID.measurable_pool EdgeIID.map_keys_pool
    (fun key (e : EdgeCode) => AllPairAllocation.coordinateNat G key e)
    (measurable_coordinate_fixed G)
  filter_upwards [RandomReindex.ae_injective_infinitePi (J := ℕ) uniform01] with key hk
  exact AllPairAllocation.coordinateNat_injective hc hf hk

theorem map_raw (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (raw G) = Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  have h := congrArg (fun μ : Measure ((ℕ → ℝ) × (EdgeCode → ℝ)) => μ.map Prod.snd)
    (map_keys_raw G hc hf)
  rw [Measure.map_map measurable_snd
      (EdgeIID.measurable_keys.prodMk (Measurable.of_eval (measurable_raw G))),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

def uniformRule (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ := by
  classical
  exact if Function.Injective (EdgeIID.keys U) then raw G U e else 0

theorem measurable_uniformRule :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      uniformRule q.1.1 q.1.2 q.2) := by
  classical
  exact Measurable.ite
    (measurable_injective_keyField.comp
      (EdgeIID.measurable_keys.comp measurable_fst.snd)).setOf
    measurable_raw_joint measurable_const

theorem measurable_uniformRule_uncurried :
    Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      uniformRule q.1 q.2.1 q.2.2) :=
  measurable_uniformRule.comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem measurable_uniformRule_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => uniformRule G U e) :=
  measurable_uniformRule.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem raw_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ)
    (hk : Function.Injective (EdgeIID.keys U)) (e : EdgeCode) :
    raw (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = raw G U e := by
  unfold raw
  rw [show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
    AllPairAllocation.coordinateNat_relabel σ G hk]
  simp [EdgeIID.pool, EdgeIID.expanded, relabelLabels]

theorem uniformRule_equivariant (σ : Equiv ℕ ℕ) (G : GraphCode)
    (U : ℕ → ℝ) (e : EdgeCode) :
    uniformRule (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      uniformRule G U e := by
  by_cases hk : Function.Injective (EdgeIID.keys U)
  · simp only [uniformRule,
      show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
      injective_relabelLabels_iff, hk, ite_true]
    exact raw_relabel σ G U hk e
  · simp only [uniformRule,
      show EdgeIID.keys (relabelLabels σ U) = relabelLabels σ (EdgeIID.keys U) from rfl,
      injective_relabelLabels_iff, hk, ite_false]

theorem map_uniformRule (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G) :
    privatePoolLaw.map (uniformRule G) =
      Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  rw [← map_raw G hc hf]
  apply Measure.map_congr
  filter_upwards [EdgeIID.ae_injective_keys] with U hU
  funext e
  simp [uniformRule, hU]

theorem uniformRule_law {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω e => uniformRule G (fun v => U v ω) e) =
      Measure.infinitePi (fun _ : EdgeCode => uniform01) := by
  have hm : Measurable (fun ω v => U v ω) := Measurable.of_eval hU.1
  rw [show (fun ω e => uniformRule G (fun v => U v ω) e) =
      uniformRule G ∘ (fun ω v => U v ω) from rfl,
    ← Measure.map_map (Measurable.of_eval (measurable_uniformRule_fixed G)) hm,
    CanonicalIID.map_labels hU]
  exact map_uniformRule G hc hf

theorem sampled_uniformRule_law {Ω Y : Type} [MeasurableSpace Ω]
    [MeasurableSpace Y] (ν : Measure Y)
    (sample : ℝ → Y) (hsample : Measurable sample)
    (hsample_law : uniform01.map sample = ν)
    (G : GraphCode) (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω e => sample (uniformRule G (fun v => U v ω) e)) =
      Measure.infinitePi (fun _ : EdgeCode => ν) := by
  have hm : Measurable (fun ω e => uniformRule G (fun v => U v ω) e) :=
    (Measurable.of_eval (measurable_uniformRule_fixed G)).comp
      (Measurable.of_eval hU.1)
  have hs : Measurable (fun x : EdgeCode → ℝ => fun e => sample (x e)) :=
    Measurable.of_eval (fun e => hsample.comp (measurable_pi_apply e))
  rw [show (fun ω e => sample (uniformRule G (fun v => U v ω) e)) =
      (fun x : EdgeCode → ℝ => fun e => sample (x e)) ∘
        (fun ω e => uniformRule G (fun v => U v ω) e) from rfl,
    ← Measure.map_map hs hm, uniformRule_law G hc hf P U hU,
    Measure.infinitePi_map_pi]
  · simp only [hsample_law]
  · intro e
    exact hsample

theorem exists_equivariant_all_pair_iid_sampler {Y : Type} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] :
    ∃ Ψ : GraphCode → (ℕ → ℝ) → EdgeCode → Y,
      Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) => Ψ q.1 q.2.1 q.2.2) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
        Ψ (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Ψ G U e) ∧
      ∀ (G : GraphCode), GraphConnected G → GraphLocallyFinite G →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ),
          IsVertexIID P U →
          P.map (fun ω e => Ψ G (fun v => U v ω) e) =
            Measure.infinitePi (fun _ : EdgeCode => ν) := by
  obtain ⟨sample, hm, hlaw⟩ := exists_uniform01_sampler ν
  refine ⟨fun G U e => sample (uniformRule G U e),
    hm.comp measurable_uniformRule_uncurried, ?_, ?_⟩
  · intro σ G U e
    exact congrArg sample (uniformRule_equivariant σ G U e)
  · intro G hc hf Ω _ P U hU
    exact sampled_uniformRule_law ν sample hm hlaw G hc hf P U hU

end Problem336.AllPairIID

end

end OAI
