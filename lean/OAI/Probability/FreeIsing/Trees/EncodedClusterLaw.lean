import OAI.Probability.FreeIsing.Trees.ClusterFactorAssembly
import OAI.Probability.FreeIsing.Trees.ClusterFactorMap
import OAI.Probability.FreeIsing.Trees.EdgeIIDLaw
import OAI.Probability.FreeIsing.Trees.FiniteClusterSelectorLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Problem367.EncodedClusterLaw

open EdgeLabelCoding EdgeIIDLaw ClusterAssembly

abbrev Environment (d : ℕ) :=
  (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ)

def codedBond {d : ℕ} (theta : ℝ) (e : TreeVertex d × TreeVertex d)
    (q : Environment d) : Bool :=
  if edgeLabel q.1 q.2 e.1 e.2 ≤ theta then true else false

theorem measurable_codedBond {d : ℕ} (theta : ℝ)
    (e : TreeVertex d × TreeVertex d) : Measurable (codedBond theta e) := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  exact Measurable.ite (measurableSet_le (measurable_edgeLabel e.1 e.2) measurable_const)
    measurable_const measurable_const

def inducedEdge {d : ℕ} (D : Finset (TreeVertex d))
    (e : inducedEdges D) : TreeEdge d := by
  classical
  exact ⟨e.val, (Finset.mem_filter.mp e.property).2⟩

theorem inducedEdge_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (inducedEdge D) := by
  intro e f h
  apply Subtype.ext
  exact congrArg (fun x : TreeEdge d => x.val) h

theorem measurePreserving_single_edge (d : ℕ) (e : TreeEdge d) :
    MeasurePreserving (fun q : Environment d => edgeLabels q.1 q.2 e)
      (codingMeasure d) uniform01 :=
  (measurePreserving_eval_infinitePi (fun _ : TreeEdge d => uniform01) e).comp
    (measurePreserving_edgeLabels d)

theorem iIndepFun_coded_edges (d : ℕ) :
    iIndepFun (fun e : TreeEdge d => fun q : Environment d => edgeLabels q.1 q.2 e)
      (codingMeasure d) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  let : IsProbabilityMeasure (codingMeasure d) := by
    unfold codingMeasure
    infer_instance
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun e => (measurePreserving_single_edge d e).measurable)).mpr
  simp_rw [(measurePreserving_single_edge d _).map_eq]
  exact (measurePreserving_edgeLabels d).map_eq

theorem iIndepFun_codedBond {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d)) :
    iIndepFun (fun e : inducedEdges D => codedBond theta e.val) (codingMeasure d) := by
  have hi := iIndepFun.precomp (inducedEdge_injective D) (iIndepFun_coded_edges d)
  have hm : Measurable (fun x : ℝ => if x ≤ theta then true else false) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  exact hi.comp (fun _ x => if x ≤ theta then true else false) (fun _ => hm)

theorem codedBond_true {d : ℕ} {theta : ℝ} (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (e : inducedEdges D) :
    codingMeasure d {q | codedBond theta e.val q = true} = ENNReal.ofReal theta := by
  have h := (measurePreserving_single_edge d (inducedEdge D e)).measure_preimage (s := Set.Iic theta)
    measurableSet_Iic.nullMeasurableSet
  rw [EdgePercolationLaw.uniform01_Iic h1] at h
  convert h using 1
  congr 1
  ext q
  simp [codedBond, edgeLabels, inducedEdge]

theorem codedBond_false {d : ℕ} {theta : ℝ} (h0 : 0 ≤ theta)
    (D : Finset (TreeVertex d)) (e : inducedEdges D) :
    codingMeasure d {q | codedBond theta e.val q = false} = ENNReal.ofReal (1 - theta) := by
  have h := (measurePreserving_single_edge d (inducedEdge D e)).measure_preimage (s := Set.Ioi theta)
    measurableSet_Ioi.nullMeasurableSet
  rw [EdgePercolationLaw.uniform01_Ioi h0] at h
  convert h using 1
  congr 1
  ext q
  simp [codedBond, edgeLabels, inducedEdge, not_le]

def productFactor {d : ℕ} (theta : ℝ)
    (q : Environment d × (TreeVertex d → ℝ)) : TreeVertex d → IsingSpin :=
  ClusterFactorMap.factor theta (q.1.1, (q.1.2, q.2))

theorem measurable_productFactor {d : ℕ} (theta : ℝ) :
    Measurable (@productFactor d theta) :=
  (ClusterFactorMap.measurable_factor theta).comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem hasFreeIsingLaw_productFactor_of_colorLaw {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hcolor : ∀ D, ConnectedFinset D → ∀ eta : TreeVertex d → IsingSpin,
      ∀ᵐ ω ∂codingMeasure d,
        labelMeasure d {c | ∀ v ∈ D, productFactor theta (ω, c) v = eta v} =
          ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D)
            (openMask (inducedEdges D) (codedBond theta) ω).val eta)) :
    HasFreeIsingLaw theta (Measure.map (productFactor theta)
      ((codingMeasure d).prod (labelMeasure d))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  exact hasFreeIsingLaw_map_prod_of_independent_bonds
    (codingMeasure d) (labelMeasure d) h0 h1 (codedBond theta)
    (measurable_codedBond theta) (iIndepFun_codedBond theta)
    (fun D e he => codedBond_true h1 D ⟨e, he⟩)
    (fun D e he => codedBond_false h0 D ⟨e, he⟩)
    (productFactor theta) (measurable_productFactor theta) hcolor

theorem hasFreeIsingLaw_factor_of_colorLaw {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hcolor : ∀ D, ConnectedFinset D → ∀ eta : TreeVertex d → IsingSpin,
      ∀ᵐ ω ∂codingMeasure d,
        labelMeasure d {c | ∀ v ∈ D, productFactor theta (ω, c) v = eta v} =
          ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D)
            (openMask (inducedEdges D) (codedBond theta) ω).val eta)) :
    HasFreeIsingLaw theta (Measure.map (ClusterFactorMap.factor theta)
      ((labelMeasure d).prod ((rowMeasure d).prod (labelMeasure d)))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have h := hasFreeIsingLaw_productFactor_of_colorLaw h0 h1 hcolor
  have hmap : Measure.map (productFactor theta)
      ((codingMeasure d).prod (labelMeasure d)) =
      Measure.map (ClusterFactorMap.factor theta)
        ((labelMeasure d).prod ((rowMeasure d).prod (labelMeasure d))) := by
    change Measure.map (ClusterFactorMap.factor theta ∘ MeasurableEquiv.prodAssoc)
      (((labelMeasure d).prod (rowMeasure d)).prod (labelMeasure d)) = _
    rw [← Measure.map_map (ClusterFactorMap.measurable_factor theta)
      MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod]
  rwa [hmap] at h

def environmentRelation {d : ℕ} (theta : ℝ) (q : Environment d)
    (u v : TreeVertex d) : Prop :=
  treeAdj u v ∧ edgeLabel q.1 q.2 u v ≤ theta

theorem openMask_eq_filter {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (q : Environment d) :
    (openMask (inducedEdges D) (codedBond theta) q).val =
      (inducedEdges D).filter (fun e => environmentRelation theta q e.1 e.2) := by
  classical
  apply Finset.filter_congr
  intro e he
  have hadj := (Finset.mem_filter.mp he).2.1
  simp [codedBond, environmentRelation, hadj]

theorem colorLaw_of_ae_finite {d : ℕ} (theta : ℝ)
    (hfinite : ∀ᵐ q ∂codingMeasure d, ∀ v : TreeVertex d,
      {a | Relation.ReflTransGen (environmentRelation theta q) v a}.Finite)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : TreeVertex d → IsingSpin) :
    ∀ᵐ q ∂codingMeasure d,
      labelMeasure d {c | ∀ v ∈ D, productFactor theta (q, c) v = eta v} =
        ENNReal.ofReal (FiniteCluster.colorWeight (inducedEdges D)
          (openMask (inducedEdges D) (codedBond theta) q).val eta) := by
  have hinj := (measurePreserving_fst (μ := labelMeasure d) (ν := rowMeasure d)).quasiMeasurePreserving.ae
    (FiniteCluster.ae_uniform_markers_injective d)
  filter_upwards [hfinite, hinj] with q hf hi
  rw [openMask_eq_filter]
  have hs : ∀ {u v}, environmentRelation theta q u v → environmentRelation theta q v u := by
    intro u v huv
    refine ⟨huv.1.symm, ?_⟩
    rw [edgeLabel_swap hi q.2 huv.1]
    exact huv.2
  exact FiniteCluster.clusterColor_cylinder_eq_colorWeight
    (fun h => h.1) hs q.1 hf hi hD eta

theorem hasFreeIsingLaw_factor_of_ae_finite {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hfinite : ∀ᵐ q ∂codingMeasure d, ∀ v : TreeVertex d,
      {a | Relation.ReflTransGen (environmentRelation theta q) v a}.Finite) :
    HasFreeIsingLaw theta (Measure.map (ClusterFactorMap.factor theta)
      ((labelMeasure d).prod ((rowMeasure d).prod (labelMeasure d)))) :=
  hasFreeIsingLaw_factor_of_colorLaw h0 h1 (colorLaw_of_ae_finite theta hfinite)

end Problem367.EncodedClusterLaw

end

end OAI
