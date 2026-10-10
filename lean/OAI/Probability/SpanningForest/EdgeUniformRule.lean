import OAI.Probability.SpanningForest.EdgeIID
import OAI.Probability.SpanningForest.EdgeAllocationMeasurable
import OAI.Probability.SpanningForest.NoCollisionExtension

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def vertexKeys (U : ℕ → ℝ) : ℕ → ℝ := EdgeIID.keys U

def vertexPools (U : ℕ → ℝ) : (ℕ × ℕ) → ℝ := EdgeIID.pool U

@[fun_prop]
theorem measurable_vertexKeys : Measurable vertexKeys := EdgeIID.measurable_keys

@[fun_prop]
theorem measurable_vertexPools : Measurable vertexPools := EdgeIID.measurable_pool

@[fun_prop]
theorem measurable_injective_keyField :
    Measurable (fun key : ℕ → ℝ => Function.Injective key) := by
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro j
  exact (measurableSet_setOfPred.mp
    (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j))).imp
      measurable_const

@[simp]
theorem vertexKeys_relabel (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) :
    vertexKeys (relabelLabels σ U) = relabelLabels σ (vertexKeys U) := rfl

def edgeUniformRule (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ := by
  classical
  exact if Function.Injective (vertexKeys U) then
    vertexPools U (EdgeAllocation.coordinate G (vertexKeys U) e)
  else 0

theorem edgeUniformRule_of_injective (G : GraphCode) {U : ℕ → ℝ}
    (hU : Function.Injective (vertexKeys U)) (e : EdgeCode) :
    edgeUniformRule G U e =
      vertexPools U (EdgeAllocation.coordinate G (vertexKeys U) e) := by
  simp [edgeUniformRule, hU]

@[fun_prop]
theorem measurable_edgeUniformRule :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      edgeUniformRule q.1.1 q.1.2 q.2) := by
  classical
  have hkeys : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      vertexKeys q.1.2) := measurable_vertexKeys.comp measurable_fst.snd
  have hpool : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      vertexPools q.1.2) := measurable_vertexPools.comp measurable_fst.snd
  have hcoord : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      EdgeAllocation.coordinate q.1.1 (vertexKeys q.1.2) q.2) :=
    EdgeAllocation.measurable_coordinate.comp
      ((measurable_fst.fst.prodMk hkeys).prodMk measurable_snd)
  have heval : Measurable
      (fun p : ((ℕ × ℕ) → ℝ) × (ℕ × ℕ) => p.1 p.2) :=
    measurable_from_prod_countable_left fun p => measurable_pi_apply p
  exact Measurable.ite
    (measurable_injective_keyField.comp hkeys).setOf
    (heval.comp (hpool.prodMk hcoord)) measurable_const

theorem measurable_edgeUniformRule_uncurried :
    Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      edgeUniformRule q.1 q.2.1 q.2.2) :=
  measurable_edgeUniformRule.comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem edgeUniformRule_equivariant (σ : Equiv ℕ ℕ) (G : GraphCode)
    (U : ℕ → ℝ) (e : EdgeCode) :
    edgeUniformRule (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      edgeUniformRule G U e := by
  by_cases hk : Function.Injective (vertexKeys U)
  · simp only [edgeUniformRule, vertexKeys_relabel, injective_relabelLabels_iff,
      hk, ite_true, EdgeAllocation.coordinate_relabel σ G hk]
    simp [vertexPools, EdgeIID.pool, EdgeIID.expanded, relabelLabels]
  · simp [edgeUniformRule, injective_relabelLabels_iff, hk]

theorem edgeUniformRule_eq_raw (G : GraphCode) (U : ℕ → ℝ)
    (hU : Function.Injective (EdgeIID.keys U)) (e : EdgeCode) :
    edgeUniformRule G U e = EdgeIID.raw G U e := by
  exact edgeUniformRule_of_injective G hU e

@[fun_prop]
theorem measurable_edgeUniformRule_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => edgeUniformRule G U e) :=
  measurable_edgeUniformRule.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

theorem edgeUniformRule_law {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hG : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω => fun e : EdgeIID.GraphEdge G =>
      edgeUniformRule G (fun v => U v ω) e) =
      Measure.infinitePi (fun _ : EdgeIID.GraphEdge G => uniform01) :=
  EdgeIID.map_rule_of_vertexIID G hG P U hU (edgeUniformRule G)
    (measurable_edgeUniformRule_fixed G) (edgeUniformRule_eq_raw G)

theorem sampled_edgeUniformRule_law {Ω Y : Type} [MeasurableSpace Ω]
    [MeasurableSpace Y] (ν : Measure Y)
    (sample : ℝ → Y) (hsample : Measurable sample)
    (hsample_law : uniform01.map sample = ν)
    (G : GraphCode) (hG : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U) :
    P.map (fun ω => fun e : EdgeIID.GraphEdge G =>
      sample (edgeUniformRule G (fun v => U v ω) e)) =
      Measure.infinitePi (fun _ : EdgeIID.GraphEdge G => ν) :=
  EdgeIID.map_sampled_rule_of_vertexIID ν sample hsample hsample_law
    G hG P U hU (edgeUniformRule G) (measurable_edgeUniformRule_fixed G)
    (edgeUniformRule_eq_raw G)

theorem exists_equivariant_edge_iid_sampler {Y : Type} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] :
    ∃ Ψ : GraphCode → (ℕ → ℝ) → EdgeCode → Y,
      Measurable (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) => Ψ q.1 q.2.1 q.2.2) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
        Ψ (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) = Ψ G U e) ∧
      ∀ (G : GraphCode), GraphLocallyFinite G →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ),
          IsVertexIID P U →
          P.map (fun ω => fun e : EdgeIID.GraphEdge G => Ψ G (fun v => U v ω) e) =
            Measure.infinitePi (fun _ : EdgeIID.GraphEdge G => ν) := by
  obtain ⟨sample, hm, hlaw⟩ := exists_uniform01_sampler ν
  refine ⟨fun G U e => sample (edgeUniformRule G U e),
    hm.comp measurable_edgeUniformRule_uncurried, ?_, ?_⟩
  · intro σ G U e
    exact congrArg sample (edgeUniformRule_equivariant σ G U e)
  · intro G hG Ω _ P U hU
    exact sampled_edgeUniformRule_law ν sample hm hlaw G hG P U hU

end Problem336

end

end OAI
