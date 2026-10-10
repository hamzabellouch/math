import OAI.Probability.FreeIsing.Trees.EdgeIIDLaw
import OAI.Probability.FreeIsing.Trees.PercolationFiniteness

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.CodedPercolation

open EdgeIIDLaw

def incomingEdge {d : ℕ} (v : TreeVertex d) (hv : v.1 ≠ []) :
    EdgeLabelCoding.TreeEdge d :=
  ⟨(parentVertex v, v), treeAdj_parentVertex hv, by
    have hpos : 0 < v.1.length := List.length_pos_iff.mpr hv
    simp only [parentVertex_length]
    omega⟩

def incomingLabel {d : ℕ} (W : TreeVertex d → VertexInput) (v : TreeVertex d) : ℝ :=
  vertexEdgeLabel W (parentVertex v) v

theorem measurable_incomingLabel {d : ℕ} (v : TreeVertex d) :
    Measurable (fun W : TreeVertex d → VertexInput => incomingLabel W v) := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  exact (EdgeLabelCoding.measurable_edgeLabel (parentVertex v) v).comp
    (measurePreserving_splitVertexInputs d).measurable

theorem incoming_all_open {d : ℕ} {theta : ℝ} (h1 : theta ≤ 1)
    (S : Finset (TreeVertex d)) (hS : ∀ v ∈ S, v.1 ≠ []) :
    vertexInputMeasure d {W | ∀ v ∈ S, incomingLabel W v ≤ theta} =
      ENNReal.ofReal theta ^ S.card := by
  classical
  let f : S → EdgeLabelCoding.TreeEdge d := fun v => incomingEdge v.1 (hS v.1 v.2)
  let D : Finset (EdgeLabelCoding.TreeEdge d) := S.attach.image f
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun e : EdgeLabelCoding.TreeEdge d => e.1.2) h
  have hcard : D.card = S.card := by
    change (S.attach.image f).card = S.card
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hevent : {W : TreeVertex d → VertexInput | ∀ v ∈ S, incomingLabel W v ≤ theta} =
      {W | ∀ e ∈ D, vertexEdgeLabels W e ≤ theta} := by
    ext W
    constructor
    · intro h e he
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
      exact h v.1 v.2
    · intro h v hv
      exact h (f ⟨v, hv⟩) (Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩)
  rw [hevent, vertex_coded_all_open d h1 D, hcard]

def openRelation {d : ℕ} (theta : ℝ) (W : TreeVertex d → VertexInput)
    (u v : TreeVertex d) : Prop :=
  treeAdj u v ∧ vertexEdgeLabel W u v ≤ theta

theorem measurableSet_openRelation {d : ℕ} (theta : ℝ) (u v : TreeVertex d) :
    MeasurableSet {W : TreeVertex d → VertexInput | openRelation theta W u v} := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  have hm : Measurable (fun W : TreeVertex d → VertexInput => vertexEdgeLabel W u v) :=
    (EdgeLabelCoding.measurable_edgeLabel u v).comp
      (measurePreserving_splitVertexInputs d).measurable
  exact (MeasurableSet.const (treeAdj u v)).inter (measurableSet_le hm measurable_const)

theorem openRelation_relabel {d : ℕ} (theta : ℝ) (g : TreeAut d)
    (W : TreeVertex d → VertexInput) (u v : TreeVertex d) :
    openRelation theta (relabel g W) (g.toEquiv u) (g.toEquiv v) ↔
      openRelation theta W u v := by
  simp only [openRelation, g.map_adj, vertexEdgeLabel_relabel]

theorem openAdj_incoming_eq {d : ℕ} (theta : ℝ) (W : TreeVertex d → VertexInput)
    (hsym : ∀ u v, treeAdj u v → vertexEdgeLabel W v u = vertexEdgeLabel W u v) :
    OpenCluster.openAdj (fun v => incomingLabel W v ≤ theta) = openRelation theta W := by
  funext u v
  apply propext
  by_cases hadj : treeAdj u v
  · by_cases hlt : u.1.length < v.1.length
    · have hp := treeAdj_parent_of_length_lt hadj hlt
      simp only [OpenCluster.openAdj, openRelation, hadj, true_and, ite_eq_left hlt,
        incomingLabel, hp]
    · have hrev : v.1.length < u.1.length := by
        rcases treeAdj_length hadj with h | h <;> omega
      have hp := treeAdj_parent_of_length_lt hadj.symm hrev
      simp only [OpenCluster.openAdj, openRelation, hadj, true_and, ite_eq_right hlt,
        incomingLabel, hp, hsym u v hadj]
  · simp only [OpenCluster.openAdj, openRelation, hadj, false_and]

theorem ae_all_finite_coded_clusters {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hsub : (d - 1 : ℕ) * theta < 1) :
    ∀ᵐ W ∂vertexInputMeasure d, ∀ o : TreeVertex d,
      {v | Relation.ReflTransGen (openRelation theta W) o v}.Finite := by
  have hfin := SubcriticalClusters.ae_all_finite_openClusters_of_cylinder_bound
    (vertexInputMeasure d) incomingLabel hsub h0
    (fun S hS => (incoming_all_open h1 S hS).le)
  filter_upwards [hfin, ae_vertexEdgeLabel_symmetric d] with W hW hsym
  intro o
  have hrel := openAdj_incoming_eq theta W hsym
  simpa only [SubcriticalClusters.openCluster, hrel] using hW o

end Problem367.CodedPercolation

end

end OAI
