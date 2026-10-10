import OAI.Probability.FreeIsing.Critical.Percolation
import OAI.Probability.FreeIsing.Trees.CodedPercolation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.CodedPercolation

open EdgeIIDLaw TreeConeCoding

theorem measurePreserving_incoming_cone {b : ℕ}
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    MeasurePreserving
      (fun W : TreeVertex (b + 1) → VertexInput => labels r hr (incomingLabel W))
      (vertexInputMeasure (b + 1)) (BranchingSurvival.wordMeasure b) := by
  have hnon (w : List (Fin b)) : (vertex r hr w).1 ≠ [] := by
    intro hnil
    have hlen := length_vertex r hr w
    have hrlen : 0 < r.1.length := List.length_pos_iff.mpr hr
    rw [hnil, List.length_nil] at hlen
    omega
  let e : List (Fin b) → EdgeLabelCoding.TreeEdge (b + 1) :=
    fun w => incomingEdge (vertex r hr w) (hnon w)
  have hinj : Function.Injective e := by
    intro w z h
    apply vertex_injective r hr
    exact congrArg (fun a : EdgeLabelCoding.TreeEdge (b + 1) => a.1.2) h
  have hm : MeasurePreserving
      (fun Y : EdgeLabelCoding.TreeEdge (b + 1) → ℝ => fun w => Y (e w))
      (edgeMeasure (b + 1)) (BranchingSurvival.wordMeasure b) :=
    ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj hinj⟩
  exact hm.comp (measurePreserving_vertexEdgeLabels (b + 1))

theorem ae_all_finite_coded_clusters_critical {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ≤ 1) :
    ∀ᵐ W ∂vertexInputMeasure d, ∀ o : TreeVertex d,
      {v | Relation.ReflTransGen (openRelation theta W) o v}.Finite := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hb : 2 ≤ b := by omega
  have hc : (b : ℝ) * theta ≤ 1 := by simpa using hcritical
  have hfinite : ∀ᵐ W ∂vertexInputMeasure (b + 1),
      ∀ r : TreeVertex (b + 1), r.1 ≠ [] →
        {v | SubcriticalClusters.DownwardOpen theta (incomingLabel W) r v}.Finite := by
    apply ae_all_iff.2
    intro r
    apply ae_all_iff.2
    intro hr
    have hext := (measurePreserving_incoming_cone r hr).quasiMeasurePreserving.ae
      (BranchingSurvival.ae_exists_extinction_depth hb ⟨h0, h1⟩ hc)
    filter_upwards [hext] with W hW
    obtain ⟨n, hn⟩ := hW
    apply (SubcriticalClusters.finite_downwardOpen_iff theta (incomingLabel W) r).2
    refine ⟨n, ?_⟩
    intro hsurv
    apply hn
    apply (survives_iff_rootedPathOpen theta n _).2
    exact (survival_iff theta (incomingLabel W) r hr n).1 hsurv
  filter_upwards [hfinite, ae_vertexEdgeLabel_symmetric (b + 1)] with W hW hsym
  intro o
  have hfin := OpenCluster.finite_reachable_of_finite_downwardOpen
    (fun v => incomingLabel W v ≤ theta)
    (SubcriticalClusters.finite_downwardOpen_of_nonroot theta (incomingLabel W) hW) o
  simpa only [openAdj_incoming_eq theta W hsym] using hfin

end Problem367.CodedPercolation

end

end OAI
