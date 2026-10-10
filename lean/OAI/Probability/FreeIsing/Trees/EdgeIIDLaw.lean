import OAI.Probability.FreeIsing.Estimates.InfinitePiPair
import OAI.Probability.FreeIsing.Estimates.RandomIndexSampling
import OAI.Probability.FreeIsing.Trees.EdgeLabelCoding
import OAI.Probability.FreeIsing.Trees.EdgePercolationLaw
import OAI.Probability.FreeIsing.Trees.FiniteClusterSelector

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.EdgeIIDLaw

abbrev rowMeasure (d : ℕ) : Measure (TreeVertex d × ℕ → ℝ) :=
  Measure.infinitePi (fun _ => uniform01)

abbrev edgeMeasure (d : ℕ) : Measure (EdgeLabelCoding.TreeEdge d → ℝ) :=
  Measure.infinitePi (fun _ => uniform01)

def codingMeasure (d : ℕ) :
    Measure ((TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ)) :=
  (labelMeasure d).prod (rowMeasure d)

theorem measurePreserving_priority_edgeLabels (d : ℕ) :
    MeasurePreserving
      (fun q : (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ) =>
        (q.1, EdgeLabelCoding.edgeLabels q.1 q.2))
      (codingMeasure d) ((labelMeasure d).prod (edgeMeasure d)) := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  apply RandomIndexSampling.measurePreserving_select (labelMeasure d) uniform01
    (r := fun p (e : EdgeLabelCoding.TreeEdge d) =>
      EdgeLabelCoding.edgeIndex p e.1.1 e.1.2)
  · intro e
    exact EdgeLabelCoding.measurable_edgeIndex e.1.1 e.1.2
  · filter_upwards [FiniteCluster.ae_uniform_markers_injective d] with p hp
    exact EdgeLabelCoding.edgeIndex_injective hp

theorem measurePreserving_edgeLabels (d : ℕ) :
    MeasurePreserving
      (fun q : (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ) =>
        EdgeLabelCoding.edgeLabels q.1 q.2)
      (codingMeasure d) (edgeMeasure d) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  exact measurePreserving_snd.comp (measurePreserving_priority_edgeLabels d)

theorem measurePreserving_environment_edgeLabels {A : Type*} [MeasurableSpace A]
    (d : ℕ) (ν : Measure A) [IsProbabilityMeasure ν] :
    MeasurePreserving
      (fun q : ((TreeVertex d → ℝ) × A) × (TreeVertex d × ℕ → ℝ) =>
        (q.1, EdgeLabelCoding.edgeLabels q.1.1 q.2))
      (((labelMeasure d).prod ν).prod (rowMeasure d))
      (((labelMeasure d).prod ν).prod (edgeMeasure d)) := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  apply RandomIndexSampling.measurePreserving_select ((labelMeasure d).prod ν) uniform01
    (r := fun (p : (TreeVertex d → ℝ) × A) (e : EdgeLabelCoding.TreeEdge d) =>
      EdgeLabelCoding.edgeIndex p.1 e.1.1 e.1.2)
  · intro e
    exact (EdgeLabelCoding.measurable_edgeIndex e.1.1 e.1.2).comp measurable_fst
  · have h := (measurePreserving_fst (μ := labelMeasure d) (ν := ν)).quasiMeasurePreserving.ae
      (FiniteCluster.ae_uniform_markers_injective d)
    filter_upwards [h] with p hp
    exact EdgeLabelCoding.edgeIndex_injective hp

theorem coded_all_open (d : ℕ) {theta : ℝ} (h1 : theta ≤ 1)
    (D : Finset (EdgeLabelCoding.TreeEdge d)) :
    codingMeasure d {q | ∀ e ∈ D, EdgeLabelCoding.edgeLabels q.1 q.2 e ≤ theta} =
      ENNReal.ofReal theta ^ D.card :=
  EdgePercolationLaw.all_open_of_measurePreserving (measurePreserving_edgeLabels d) h1 D

theorem coded_joint_cylinder (d : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (B : Set (TreeVertex d → ℝ)) (hB : MeasurableSet B)
    (D : Finset (EdgeLabelCoding.TreeEdge d)) (status : EdgeLabelCoding.TreeEdge d → Bool) :
    codingMeasure d {q | q.1 ∈ B ∧ ∀ e ∈ D,
      EdgeLabelCoding.edgeLabels q.1 q.2 e ∈ EdgePercolationLaw.edgeInterval theta (status e)} =
      labelMeasure d B *
        ∏ e ∈ D, if status e then ENNReal.ofReal theta else ENNReal.ofReal (1 - theta) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  exact EdgePercolationLaw.joint_cylinder_of_measurePreserving
    (measurePreserving_priority_edgeLabels d) h0 h1 B hB D status

abbrev VertexInput := ℝ × (ℕ → ℝ)

abbrev vertexInputLaw : Measure VertexInput :=
  uniform01.prod (Measure.infinitePi (fun _ : ℕ => uniform01))

abbrev vertexInputMeasure (d : ℕ) : Measure (TreeVertex d → VertexInput) :=
  Measure.infinitePi (fun _ => vertexInputLaw)

def splitVertexInputs {d : ℕ} (W : TreeVertex d → VertexInput) :
    (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ) :=
  (fun v => (W v).1, fun p => (W p.1).2 p.2)

theorem measurePreserving_splitVertexInputs (d : ℕ) :
    MeasurePreserving splitVertexInputs (vertexInputMeasure d) (codingMeasure d) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have hs : MeasurePreserving
      (fun W : TreeVertex d → VertexInput => (fun v => (W v).1, fun v => (W v).2))
      (vertexInputMeasure d)
      ((labelMeasure d).prod
        (Measure.infinitePi (fun _ : TreeVertex d =>
          Measure.infinitePi (fun _ : ℕ => uniform01)))) :=
    ⟨by fun_prop, infinitePi_map_split_pairs (fun _ => uniform01)
      (fun _ => Measure.infinitePi (fun _ : ℕ => uniform01))⟩
  have hu : MeasurePreserving
      (fun Z : TreeVertex d → ℕ → ℝ => fun p : TreeVertex d × ℕ => Z p.1 p.2)
      (Measure.infinitePi (fun _ : TreeVertex d =>
        Measure.infinitePi (fun _ : ℕ => uniform01))) (rowMeasure d) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry_symm (fun (_ : TreeVertex d) (_ : ℕ) => uniform01)⟩
  exact ((MeasurePreserving.id (labelMeasure d)).prod hu).comp hs

def vertexEdgeLabels {d : ℕ} (W : TreeVertex d → VertexInput) :
    EdgeLabelCoding.TreeEdge d → ℝ :=
  EdgeLabelCoding.edgeLabels (splitVertexInputs W).1 (splitVertexInputs W).2

theorem measurePreserving_vertex_priority_edges (d : ℕ) :
    MeasurePreserving
      (fun W : TreeVertex d → VertexInput => (fun v => (W v).1, vertexEdgeLabels W))
      (vertexInputMeasure d) ((labelMeasure d).prod (edgeMeasure d)) :=
  (measurePreserving_priority_edgeLabels d).comp (measurePreserving_splitVertexInputs d)

theorem measurePreserving_vertexEdgeLabels (d : ℕ) :
    MeasurePreserving vertexEdgeLabels (vertexInputMeasure d) (edgeMeasure d) :=
  (measurePreserving_edgeLabels d).comp (measurePreserving_splitVertexInputs d)

def vertexEdgeLabel {d : ℕ} (W : TreeVertex d → VertexInput)
    (u v : TreeVertex d) : ℝ :=
  EdgeLabelCoding.edgeLabel (splitVertexInputs W).1 (splitVertexInputs W).2 u v

theorem vertexEdgeLabel_relabel {d : ℕ} (g : TreeAut d)
    (W : TreeVertex d → VertexInput) (u v : TreeVertex d) :
    vertexEdgeLabel (relabel g W) (g.toEquiv u) (g.toEquiv v) = vertexEdgeLabel W u v :=
  EdgeLabelCoding.edgeLabel_relabel g (splitVertexInputs W).1 (splitVertexInputs W).2 u v

theorem ae_vertexEdgeLabel_symmetric (d : ℕ) :
    ∀ᵐ W ∂vertexInputMeasure d, ∀ u v, treeAdj u v →
      vertexEdgeLabel W v u = vertexEdgeLabel W u v := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have hm : MeasurePreserving (fun W : TreeVertex d → VertexInput => fun v => (W v).1)
      (vertexInputMeasure d) (labelMeasure d) :=
    measurePreserving_fst.comp (measurePreserving_vertex_priority_edges d)
  filter_upwards [hm.quasiMeasurePreserving.ae (FiniteCluster.ae_uniform_markers_injective d)]
    with W hW
  intro u v huv
  exact EdgeLabelCoding.edgeLabel_swap hW (splitVertexInputs W).2 huv

theorem vertex_coded_all_open (d : ℕ) {theta : ℝ} (h1 : theta ≤ 1)
    (D : Finset (EdgeLabelCoding.TreeEdge d)) :
    vertexInputMeasure d {W | ∀ e ∈ D, vertexEdgeLabels W e ≤ theta} =
      ENNReal.ofReal theta ^ D.card :=
  EdgePercolationLaw.all_open_of_measurePreserving (measurePreserving_vertexEdgeLabels d) h1 D

end Problem367.EdgeIIDLaw

end

end OAI
