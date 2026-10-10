import OAI.Probability.FreeIsing.Estimates.FairSpin
import OAI.Probability.FreeIsing.Estimates.MeasurableConnectivity
import OAI.Probability.FreeIsing.Trees.EdgeLabelCoding
import OAI.Probability.FreeIsing.Trees.FiniteClusterSelector

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.ClusterFactorMap

open EdgeLabelCoding

variable {d : ℕ}

abbrev Input (d : ℕ) :=
  (TreeVertex d → ℝ) × ((TreeVertex d × ℕ → ℝ) × (TreeVertex d → ℝ))

def relabelInput (g : TreeAut d) (p : Input d) : Input d :=
  (relabel g p.1, ((fun q => p.2.1 (g.toEquiv.symm q.1, q.2)), relabel g p.2.2))

def openAdj (theta : ℝ) (p : Input d) (u v : TreeVertex d) : Prop :=
  treeAdj u v ∧ edgeLabel p.1 p.2.1 u v ≤ theta

def connected (theta : ℝ) (p : Input d) : TreeVertex d → TreeVertex d → Prop :=
  Relation.ReflTransGen (openAdj theta p)

def factor (theta : ℝ) (p : Input d) : TreeVertex d → IsingSpin :=
  FiniteCluster.color (connected theta p) p.1 (fun v => fairSpin (p.2.2 v))

@[simp] lemma factor_apply (theta : ℝ) (p : Input d) (v : TreeVertex d) :
    factor theta p v =
      fairSpin (p.2.2 (FiniteCluster.selector (connected theta p) p.1 v)) := rfl

lemma openAdj_edge_iff (theta : ℝ) (p : Input d) (e : TreeEdge d) :
    openAdj theta p e.1.1 e.1.2 ↔ edgeLabels p.1 p.2.1 e ≤ theta := by
  exact and_iff_right e.2.1

lemma measurable_relabelInput (g : TreeAut d) :
    Measurable (relabelInput g) := by
  unfold relabelInput relabel
  fun_prop

lemma openAdj_sub_treeAdj (theta : ℝ) (p : Input d) {u v : TreeVertex d}
    (h : openAdj theta p u v) : treeAdj u v := h.1

lemma openAdj_symmetric (theta : ℝ) {p : Input d} (hp : Function.Injective p.1) :
    ∀ ⦃u v : TreeVertex d⦄, openAdj theta p u v → openAdj theta p v u := by
  intro u v huv
  refine ⟨adj_symm huv.1, ?_⟩
  rw [edgeLabel_swap hp p.2.1 huv.1]
  exact huv.2

lemma connected_equivalence (theta : ℝ) {p : Input d}
    (hp : Function.Injective p.1) : Equivalence (connected theta p) := by
  refine ⟨fun _ => .refl, ?_, fun h h' => h.trans h'⟩
  intro u v huv
  have hsymm := openAdj_symmetric theta hp
  apply Relation.reflTransGen_swap.mp
  exact Relation.ReflTransGen.mono (fun _ _ h => hsymm h) _ _ huv

lemma openAdj_relabel (g : TreeAut d) (theta : ℝ) (p : Input d)
    (u v : TreeVertex d) :
    openAdj theta (relabelInput g p) (g.toEquiv u) (g.toEquiv v) ↔
      openAdj theta p u v := by
  simp only [openAdj, relabelInput, g.map_adj, edgeLabel_relabel]

lemma connected_relabel (g : TreeAut d) (theta : ℝ) (p : Input d)
    (u v : TreeVertex d) :
    connected theta (relabelInput g p) (g.toEquiv u) (g.toEquiv v) ↔
      connected theta p u v := by
  exact reflTransGen_equiv_iff g.toEquiv (openAdj_relabel g theta p) u v

lemma connected_relabel_eq (g : TreeAut d) (theta : ℝ) (p : Input d) :
    connected theta (relabelInput g p) =
      fun u v => connected theta p (g.toEquiv.symm u) (g.toEquiv.symm v) := by
  funext u v
  apply propext
  simpa only [Equiv.apply_symm_apply] using
    connected_relabel g theta p (g.toEquiv.symm u) (g.toEquiv.symm v)

theorem factor_relabel (g : TreeAut d) (theta : ℝ) (p : Input d) :
    factor theta (relabelInput g p) = relabel g (factor theta p) := by
  funext v
  unfold factor
  rw [connected_relabel_eq]
  have h := FiniteCluster.color_reindex g.toEquiv (connected theta p) p.1
    (fun w => fairSpin (p.2.2 w)) (g.toEquiv.symm v)
  change FiniteCluster.color
    (fun x y => connected theta p (g.toEquiv.symm x) (g.toEquiv.symm y))
    (fun x => p.1 (g.toEquiv.symm x))
    (fun x => fairSpin (p.2.2 (g.toEquiv.symm x))) v =
      FiniteCluster.color (connected theta p) p.1
        (fun x => fairSpin (p.2.2 x)) (g.toEquiv.symm v)
  simpa only [Equiv.apply_symm_apply, Function.comp_def] using h

theorem factor_eq_of_connected (theta : ℝ) {p : Input d}
    (hp : Function.Injective p.1) {u v : TreeVertex d}
    (hu : {w | connected theta p u w}.Finite) (huv : connected theta p u v) :
    factor theta p u = factor theta p v :=
  FiniteCluster.color_eq_of_related _ (connected_equivalence theta hp) huv hu hp

theorem factor_eq_at_minimum (theta : ℝ) (p : Input d) (v a : TreeVertex d)
    (ha : FiniteCluster.IsMinimum (connected theta p) p.1 v a) :
    factor theta p v = fairSpin (p.2.2 a) := by
  unfold factor FiniteCluster.color
  rw [FiniteCluster.selector_eq_of_minimum ha]

lemma measurableSet_openAdj (theta : ℝ) (u v : TreeVertex d) :
    MeasurableSet {p : Input d | openAdj theta p u v} := by
  let : MeasurableSpace (TreeVertex d) := ⊤
  let : MeasurableSingletonClass (TreeVertex d) := ⟨fun _ => trivial⟩
  have hlabel : Measurable (fun p : Input d => edgeLabel p.1 p.2.1 u v) :=
    (measurable_edgeLabel u v).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact (MeasurableSet.const (treeAdj u v)).inter
    (measurableSet_le hlabel measurable_const)

lemma measurableSet_connected (theta : ℝ) (u v : TreeVertex d) :
    MeasurableSet {p : Input d | connected theta p u v} :=
  measurableSet_reflTransGen (measurableSet_openAdj theta) u v

theorem measurable_factor (theta : ℝ) : Measurable (@factor d theta) := by
  apply FiniteCluster.measurable_color
    (connected theta) (fun p : Input d => p.1)
    (fun p : Input d => fun v => fairSpin (p.2.2 v))
  · exact measurableSet_connected theta
  · intro v
    exact (measurable_pi_apply v).comp measurable_fst
  · intro v
    exact measurable_fairSpin.comp
      ((measurable_pi_apply v).comp (measurable_snd.comp measurable_snd))

end Problem367.ClusterFactorMap

end

end OAI
