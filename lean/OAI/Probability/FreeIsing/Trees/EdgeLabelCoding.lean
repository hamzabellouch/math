import OAI.Probability.FreeIsing.Estimates.FiniteMarkerRank
import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Trees.Parents
import OAI.Probability.FreeIsing.Trees.Regularity

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem367.EdgeLabelCoding

variable {d : ℕ}

def neighborRank (m : TreeVertex d → ℝ) (v w : TreeVertex d) : ℕ :=
  FiniteMarkerRank.rank (treeNeighborFinset v) m w

lemma neighborRank_eq_card (m : TreeVertex d → ℝ) (v w : TreeVertex d) :
    neighborRank m v w = ((treeNeighborFinset v).filter (fun z => m z < m w)).card := rfl

lemma neighborRank_lt {m : TreeVertex d → ℝ} {v w w' : TreeVertex d}
    (hw : treeAdj v w) (hww' : m w < m w') :
    neighborRank m v w < neighborRank m v w' :=
  FiniteMarkerRank.rank_lt_of_marker_lt _ _ ((mem_treeNeighborFinset v w).mpr hw) hww'

lemma neighborRank_injective {m : TreeVertex d → ℝ} (hm : Function.Injective m)
    {v w w' : TreeVertex d} (hw : treeAdj v w) (hw' : treeAdj v w')
    (heq : neighborRank m v w = neighborRank m v w') : w = w' :=
  FiniteMarkerRank.rank_injOn _ _ hm.injOn ((mem_treeNeighborFinset v w).mpr hw)
    ((mem_treeNeighborFinset v w').mpr hw') heq

lemma neighborRank_lt_degree (m : TreeVertex d → ℝ) {v w : TreeVertex d}
    (hw : treeAdj v w) : neighborRank m v w < d := by
  simpa only [neighborRank, card_treeNeighborFinset] using
    FiniteMarkerRank.rank_lt_card (treeNeighborFinset v) m
      ((mem_treeNeighborFinset v w).mpr hw)

lemma measurable_neighborRank (v w : TreeVertex d) :
    Measurable (fun m : TreeVertex d → ℝ => neighborRank m v w) :=
  FiniteMarkerRank.measurable_rank (treeNeighborFinset v) w

def edgeIndex (m : TreeVertex d → ℝ) (u v : TreeVertex d) : TreeVertex d × ℕ :=
  if m u < m v then (u, neighborRank m u v) else (v, neighborRank m v u)

lemma adj_symm {u v : TreeVertex d} (h : treeAdj u v) : treeAdj v u := h.symm

lemma adj_ne {u v : TreeVertex d} (h : treeAdj u v) : u ≠ v := by
  intro heq
  subst v
  have := treeAdj_length h
  omega

lemma edgeIndex_swap {m : TreeVertex d → ℝ} (hm : Function.Injective m)
    {u v : TreeVertex d} (h : treeAdj u v) :
    edgeIndex m v u = edgeIndex m u v := by
  have hne : m u ≠ m v := fun heq => adj_ne h (hm heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp [edgeIndex, hlt, not_lt.mpr hlt.le]
  · simp [edgeIndex, hgt, not_lt.mpr hgt.le]

abbrev TreeEdge (d : ℕ) :=
  {p : TreeVertex d × TreeVertex d // treeAdj p.1 p.2 ∧ p.1.1.length < p.2.1.length}

lemma edgeIndex_injective {m : TreeVertex d → ℝ} (hm : Function.Injective m) :
    Function.Injective (fun e : TreeEdge d => edgeIndex m e.1.1 e.1.2) := by
  intro e f hef
  rcases e with ⟨⟨u, v⟩, huv, huvlen⟩
  rcases f with ⟨⟨u', v'⟩, hu'v', hu'v'len⟩
  dsimp only at huv huvlen hu'v' hu'v'len
  apply Subtype.ext
  change (u, v) = (u', v')
  change edgeIndex m u v = edgeIndex m u' v' at hef
  unfold edgeIndex at hef
  split_ifs at hef with h h'
  · have howner := congrArg Prod.fst hef
    have hrank := congrArg Prod.snd hef
    dsimp at howner hrank
    subst u'
    exact Prod.ext rfl (neighborRank_injective hm huv hu'v' hrank)
  · have howner := congrArg Prod.fst hef
    have hrank := congrArg Prod.snd hef
    dsimp at howner hrank
    subst v'
    have hother := neighborRank_injective hm huv (adj_symm hu'v') hrank
    subst u'
    omega
  · have howner := congrArg Prod.fst hef
    have hrank := congrArg Prod.snd hef
    dsimp at howner hrank
    subst u'
    have hother := neighborRank_injective hm (adj_symm huv) hu'v' hrank
    subst v'
    omega
  · have howner := congrArg Prod.fst hef
    have hrank := congrArg Prod.snd hef
    dsimp at howner hrank
    subst v'
    exact Prod.ext (neighborRank_injective hm (adj_symm huv) (adj_symm hu'v') hrank) rfl

lemma edgeIndex_snd_lt_degree (m : TreeVertex d → ℝ) {u v : TreeVertex d}
    (h : treeAdj u v) : (edgeIndex m u v).2 < d := by
  unfold edgeIndex
  split_ifs
  · exact neighborRank_lt_degree m h
  · exact neighborRank_lt_degree m (adj_symm h)

section MeasurableIndex
variable [MeasurableSpace (TreeVertex d)]

lemma measurable_edgeIndex (u v : TreeVertex d) :
    Measurable (fun m : TreeVertex d → ℝ => edgeIndex m u v) := by
  apply Measurable.ite (measurableSet_lt (measurable_pi_apply u) (measurable_pi_apply v))
  · exact measurable_const.prodMk (measurable_neighborRank u v)
  · exact measurable_const.prodMk (measurable_neighborRank v u)

lemma measurable_edgeAddresses :
    Measurable (fun m : TreeVertex d → ℝ =>
      fun e : TreeEdge d => edgeIndex m e.1.1 e.1.2) :=
  Measurable.of_eval fun edge => measurable_edgeIndex edge.1.1 edge.1.2

end MeasurableIndex

lemma treeNeighborFinset_image (g : TreeAut d) (v : TreeVertex d) :
    treeNeighborFinset (g.toEquiv v) = (treeNeighborFinset v).image g.toEquiv := by
  classical
  ext z
  simp only [mem_treeNeighborFinset, Finset.mem_image]
  constructor
  · intro hz
    refine ⟨g.toEquiv.symm z, ?_, g.toEquiv.apply_symm_apply z⟩
    apply (g.map_adj v (g.toEquiv.symm z)).mp
    simpa using hz
  · rintro ⟨w, hw, rfl⟩
    exact (g.map_adj v w).mpr hw

lemma neighborRank_relabel (g : TreeAut d) (m : TreeVertex d → ℝ)
    (v w : TreeVertex d) :
    neighborRank (relabel g m) (g.toEquiv v) (g.toEquiv w) = neighborRank m v w := by
  classical
  unfold neighborRank
  rw [treeNeighborFinset_image, FiniteMarkerRank.rank_image]
  simp only [relabel, Equiv.symm_apply_apply]

lemma edgeIndex_relabel (g : TreeAut d) (m : TreeVertex d → ℝ)
    (u v : TreeVertex d) :
    edgeIndex (relabel g m) (g.toEquiv u) (g.toEquiv v) =
      (g.toEquiv (edgeIndex m u v).1, (edgeIndex m u v).2) := by
  simp only [edgeIndex, relabel, Equiv.symm_apply_apply]
  split_ifs
  · congr 1
    exact neighborRank_relabel g m u v
  · congr 1
    exact neighborRank_relabel g m v u

def edgeLabel (m : TreeVertex d → ℝ) (Z : TreeVertex d × ℕ → ℝ)
    (u v : TreeVertex d) : ℝ := Z (edgeIndex m u v)

def edgeLabels (m : TreeVertex d → ℝ) (Z : TreeVertex d × ℕ → ℝ) : TreeEdge d → ℝ :=
  fun e => edgeLabel m Z e.1.1 e.1.2

lemma edgeLabel_swap {m : TreeVertex d → ℝ} (hm : Function.Injective m)
    (Z : TreeVertex d × ℕ → ℝ) {u v : TreeVertex d} (h : treeAdj u v) :
    edgeLabel m Z v u = edgeLabel m Z u v := by
  simp only [edgeLabel, edgeIndex_swap hm h]

lemma edgeLabel_relabel (g : TreeAut d) (m : TreeVertex d → ℝ)
    (Z : TreeVertex d × ℕ → ℝ) (u v : TreeVertex d) :
    edgeLabel (relabel g m) (fun p => Z (g.toEquiv.symm p.1, p.2))
      (g.toEquiv u) (g.toEquiv v) = edgeLabel m Z u v := by
  simp only [edgeLabel, edgeIndex_relabel, Equiv.symm_apply_apply]

section MeasurableLabel
variable [MeasurableSpace (TreeVertex d)] [MeasurableSingletonClass (TreeVertex d)]

lemma measurable_edgeLabel (u v : TreeVertex d) :
    Measurable (fun p : (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ) =>
      edgeLabel p.1 p.2 u v) := by
  have heval : Measurable (fun q : (TreeVertex d × ℕ → ℝ) × (TreeVertex d × ℕ) =>
      q.1 q.2) := measurable_from_prod_countable_left fun i => measurable_pi_apply i
  exact heval.comp (measurable_snd.prodMk ((measurable_edgeIndex u v).comp measurable_fst))

lemma measurable_edgeLabels :
    Measurable (fun p : (TreeVertex d → ℝ) × (TreeVertex d × ℕ → ℝ) =>
      edgeLabels p.1 p.2) :=
  Measurable.of_eval fun edge => measurable_edgeLabel edge.1.1 edge.1.2

end MeasurableLabel

end Problem367.EdgeLabelCoding

end

end OAI
