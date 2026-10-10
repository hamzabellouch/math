import OAI.Probability.SpanningForest.FiniteIncidenceBridge
import OAI.Probability.SpanningForest.IncidenceMinorClassification
import OAI.Probability.SpanningForest.CauchyBinet

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336.FiniteIncidence

theorem edgeAdj_comp_equiv {V E F : Type*} (s t : E → V) (e : F ≃ E) (u v : V) :
    ReducedLaplacian.EdgeAdj (s ∘ e) (t ∘ e) u v ↔
      ReducedLaplacian.EdgeAdj s t u v := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, ?_⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using ha

theorem connected_comp_equiv {V E F : Type*} (s t : E → V) (e : F ≃ E) :
    ReducedLaplacian.Connected (s ∘ e) (t ∘ e) ↔
      ReducedLaplacian.Connected s t := by
  have hrel : ReducedLaplacian.EdgeAdj (s ∘ e) (t ∘ e) =
      ReducedLaplacian.EdgeAdj s t :=
    funext fun u => funext fun v => propext (edgeAdj_comp_equiv s t e u v)
  simp only [ReducedLaplacian.Connected, hrel]

theorem squareReducedGradient_det_sq_eq_connected
    (V : Finset ℕ) (T : Finset (ℕ × ℕ)) (h : ValidEdges V T)
    (root : V) (e : T ≃ {v : V // v ≠ root}) :
    (squareReducedGradient V T h root e).det ^ 2 =
      if ReducedLaplacian.Connected (src V T h) (dst V T h) then 1 else 0 := by
  classical
  change (ReducedLaplacian.reducedGradient
    (src V T h ∘ e.symm) (dst V T h ∘ e.symm) root).det ^ 2 = _
  rw [IncidenceMinor.reducedGradient_det_sq_eq_indicator, connected_comp_equiv]

theorem squareReducedGradient_det_sq_eq_treeOn
    {G : GraphCode} {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    {T : Finset (ℕ × ℕ)} (hT : T ⊆ K.2)
    (hcard : T.card + 1 = K.1.card) (root : K.1)
    (e : T ≃ {v : K.1 // v ≠ root}) :
    (squareReducedGradient K.1 T (validEdges_of_subgraph hK hT) root e).det ^ 2 =
      if TreeOn K T then 1 else 0 := by
  classical
  rw [squareReducedGradient_det_sq_eq_connected]
  have heq : TreeOn K T ↔ ReducedLaplacian.Connected
      (src K.1 T (validEdges_of_subgraph hK hT))
      (dst K.1 T (validEdges_of_subgraph hK hT)) := by
    rw [treeOn_iff_connected hK hT]
    exact and_iff_right hcard
  simp only [← heq]

def selectedEdges {K : FiniteSubgraphCode} (s : Finset K.2) : Finset (ℕ × ℕ) :=
  s.map (Function.Embedding.subtype (fun p => p ∈ K.2))

theorem selectedEdges_subset {K : FiniteSubgraphCode} (s : Finset K.2) :
    selectedEdges s ⊆ K.2 := by
  intro p hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hp
  exact a.property

@[simp] theorem selectedEdges_card {K : FiniteSubgraphCode} (s : Finset K.2) :
    (selectedEdges s).card = s.card := Finset.card_map _

def selectedEdgeEquiv {K : FiniteSubgraphCode} (s : Finset K.2) :
    s ≃ selectedEdges s :=
  Equiv.ofBijective
    (fun e => ⟨e.val.val, Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun p : selectedEdges s => p.val) hab,
     by
      intro p
      obtain ⟨e, he, hep⟩ := Finset.mem_map.mp p.property
      exact ⟨⟨e, he⟩, Subtype.ext hep⟩⟩

theorem connected_restrict_iff_selectedEdges
    {G : GraphCode} {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (s : Finset K.2) :
    ReducedLaplacian.Connected
      (src K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)) ∘
        (Subtype.val : s → K.2))
      (dst K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)) ∘
        (Subtype.val : s → K.2)) ↔
      ReducedLaplacian.Connected
        (src K.1 (selectedEdges s) (validEdges_of_subgraph hK (selectedEdges_subset s)))
        (dst K.1 (selectedEdges s) (validEdges_of_subgraph hK (selectedEdges_subset s))) := by
  change ReducedLaplacian.Connected
      (src K.1 (selectedEdges s) (validEdges_of_subgraph hK (selectedEdges_subset s)) ∘
        selectedEdgeEquiv s)
      (dst K.1 (selectedEdges s) (validEdges_of_subgraph hK (selectedEdges_subset s)) ∘
        selectedEdgeEquiv s) ↔ _
  exact connected_comp_equiv _ _ (selectedEdgeEquiv s)

theorem connected_restrict_iff_treeOn
    {G : GraphCode} {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (s : Finset K.2) (hcard : s.card + 1 = K.1.card) :
    ReducedLaplacian.Connected
      (src K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)) ∘
        (Subtype.val : s → K.2))
      (dst K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)) ∘
        (Subtype.val : s → K.2)) ↔ TreeOn K (selectedEdges s) := by
  rw [connected_restrict_iff_selectedEdges hK s, treeOn_iff_connected hK (selectedEdges_subset s)]
  exact (and_iff_right (by simpa only [selectedEdges_card] using hcard)).symm

theorem selectedEdges_card_add_one {K : FiniteSubgraphCode} (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (selectedEdges s.val).card + 1 = K.1.card := by
  rw [selectedEdges_card, (Finset.mem_powersetCard.mp s.property).2,
    Fintype.card_subtype_compl (fun v : K.1 => v = root), Fintype.card_coe,
    Fintype.card_subtype_eq]
  have hpos : 0 < K.1.card := Finset.card_pos.mpr ⟨root.val, root.property⟩
  omega

theorem columnMinor_det_sq_eq_treeOn
    {G : GraphCode} {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (CauchyBinet.columnMinor
      (ReducedLaplacian.reducedGradient
        (src K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp)))
        (dst K.1 K.2 (validEdges_of_subgraph hK (fun _ hp => hp))) root).transpose s).det ^ 2 =
      if TreeOn K (selectedEdges s.val) then 1 else 0 := by
  let hv := validEdges_of_subgraph hK (fun _ hp => hp)
  let A := (ReducedLaplacian.reducedGradient (src K.1 K.2 hv) (dst K.1 K.2 hv) root).transpose
  let ix := CauchyBinet.columnIndexEquiv s
  let f : {v : K.1 // v ≠ root} → K.2 := fun i => (ix.symm i).val
  have hdet : (CauchyBinet.columnMinor A s).det = (A.submatrix id f).det := by
    calc
      _ = ((CauchyBinet.columnMinor A s).submatrix ix.symm ix.symm).det :=
        (Matrix.det_submatrix_equiv_self ix.symm _).symm
      _ = _ := by
        congr 1
        ext i j
        simp [CauchyBinet.columnMinor, Matrix.submatrix, ix, f]
  change (CauchyBinet.columnMinor A s).det ^ 2 = _
  rw [hdet]
  change (((ReducedLaplacian.reducedGradient
    (src K.1 K.2 hv) (dst K.1 K.2 hv) root).transpose).submatrix id f).det ^ 2 = _
  rw [IncidenceMinor.selected_minor_det_sq_eq_indicator]
  let hs := validEdges_of_subgraph hK (selectedEdges_subset s.val)
  let e : {v : K.1 // v ≠ root} ≃ selectedEdges s.val :=
    ix.symm.trans (selectedEdgeEquiv s.val)
  have hc : ReducedLaplacian.Connected (src K.1 K.2 hv ∘ f) (dst K.1 K.2 hv ∘ f) ↔
      ReducedLaplacian.Connected (src K.1 (selectedEdges s.val) hs)
        (dst K.1 (selectedEdges s.val) hs) := by
    change ReducedLaplacian.Connected
      (src K.1 (selectedEdges s.val) hs ∘ e)
      (dst K.1 (selectedEdges s.val) hs ∘ e) ↔ _
    exact connected_comp_equiv _ _ e
  rw [hc]
  have ht : TreeOn K (selectedEdges s.val) ↔
      ReducedLaplacian.Connected (src K.1 (selectedEdges s.val) hs)
        (dst K.1 (selectedEdges s.val) hs) := by
    rw [treeOn_iff_connected hK (selectedEdges_subset s.val)]
    exact and_iff_right (selectedEdges_card_add_one root s)
  simp only [← ht]

end Problem336.FiniteIncidence

end

end OAI
