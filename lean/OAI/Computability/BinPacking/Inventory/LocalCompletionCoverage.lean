import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import OAI.Computability.BinPacking.Packing.PackingCoordinates
import OAI.Computability.BinPacking.Trees.InventoryFromTrees

namespace OAI

noncomputable section

namespace BinPackingGap.PartialAllocation

theorem exists_equiv_extending_embeddings
    {I J S : Type*} [Fintype I] [Fintype J]
    (f : S ↪ I) (g : S ↪ J)
    (hcard : Fintype.card I = Fintype.card J) :
    ∃ e : I ≃ J, ∀ s, e (f s) = g s := by
  classical
  let assigned : Set.range f ≃ Set.range g :=
    (Equiv.ofInjective f f.injective).symm.trans (Equiv.ofInjective g g.injective)
  have hremaining : Fintype.card ↥((Set.range f)ᶜ) =
      Fintype.card ↥((Set.range g)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcard,
      Fintype.card_congr assigned]
  let remaining : ↥((Set.range f)ᶜ) ≃ ↥((Set.range g)ᶜ) :=
    Fintype.equivOfCardEq hremaining
  let e : I ≃ J := (Equiv.Set.sumCompl (Set.range f)).symm.trans
    ((Equiv.sumCongr assigned remaining).trans (Equiv.Set.sumCompl (Set.range g)))
  refine ⟨e, ?_⟩
  intro s
  have hfs : f s ∈ Set.range f := ⟨s, rfl⟩
  change ((Equiv.Set.sumCompl (Set.range g))
    ((Equiv.sumCongr assigned remaining)
      ((Equiv.Set.sumCompl (Set.range f)).symm (f s)))) = g s
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hfs]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  change ((Equiv.ofInjective g g.injective)
    ((Equiv.ofInjective f f.injective).symm ⟨f s, hfs⟩)).val = g s
  rw [Equiv.ofInjective_symm_apply]
  rfl

theorem exists_equiv_extending_injections
    {I J S : Type*} [Fintype I] [Fintype J]
    (f : S → I) (g : S → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcard : Fintype.card I = Fintype.card J) :
    ∃ e : I ≃ J, ∀ s, e (f s) = g s :=
  exists_equiv_extending_embeddings ⟨f, hf⟩ ⟨g, hg⟩ hcard

end BinPackingGap.PartialAllocation

namespace BinPackingGap.InventoryData

open IntervalCoverage

variable (D : InventoryData)

theorem designated_injective (v : D.Vertex) :
    Function.Injective (D.designated (v := v)) := by
  rintro ⟨(p | p | j), a⟩ ⟨(q | q | k), b⟩ h <;>
    simp_all [designated, Subtype.val_inj]

theorem deadline_undesignated {v : D.Vertex} (i : D.MBase v)
    (hi : ∀ q : D.TestAt v × Fin D.d, D.designated q ≠ i) :
    D.deadline i = D.mainBaseline i := by
  rcases i with (⟨node, j⟩ | ⟨node, j⟩ | padding) | job
  · have hn : node.val ∉ D.plus.leaves := by
      intro hn
      exact hi (.inl ⟨node, hn⟩, j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · have hn : node.val ∉ D.minus.leaves := by
      intro hn
      exact hi (.inr (.inl ⟨node, hn⟩), j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · rfl
  · exact False.elim (hi (.inr (.inr job.1), job.2) rfl)

def deadlineShiftData (v : D.Vertex) :
    ShiftData (D.MBase v) (D.TestAt v) D.d ℚ where
  baseline := D.mainBaseline
  left := D.testLeft
  right := D.testRight
  designated := ⟨D.designated, D.designated_injective v⟩
  baseline_designated := D.mainBaseline_designated
  left_le_right := fun t => (D.testLeft_lt_testRight t).le

private theorem deadline_prefix_active (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * ((D.deadlineShiftData v).activeTests a).card := by
  exact (D.deadlineShiftData v).deadline_prefix_of_agrees
    (D.deadline (v := v)) D.deadline_designated D.deadline_undesignated a

private theorem deadline_active_card (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    ((D.deadlineShiftData v).activeTests a).card =
      @ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
        (Classical.propDecidable _) 1 0 := by
  classical
  have hdisjoint : ∀ s t : D.TestAt v, s ≠ t →
      Disjoint (Set.Ico ((D.deadlineShiftData v).left s)
        ((D.deadlineShiftData v).right s))
        (Set.Ico ((D.deadlineShiftData v).left t)
        ((D.deadlineShiftData v).right t)) := by
    intro s t hst
    exact D.testInterval_disjoint hplusheight hminusheight hL hst
  have hc := (D.deadlineShiftData v).activeTests_card hdisjoint a
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht]
    have ht' : ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_left ht'] at hc
    exact hc
  · rw [ite_eq_right ht]
    have ht' : ¬ ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_right ht'] at hc
    exact hc

theorem deadline_prefix (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * (@ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
          (Classical.propDecidable _) 1 0) := by
  rw [D.deadline_prefix_active, D.deadline_active_card hplusheight hminusheight hL]

theorem deadline_prefix_at_test (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    ((Finset.univ : Finset (D.MBase v)).filter (fun z => D.deadline z ≤ a)).card =
      ((Finset.univ : Finset (D.MBase v)).filter
        (fun z => D.mainBaseline z ≤ a)).card + D.d := by
  classical
  have hex : ∃ t : D.TestAt v, a ∈ D.testInterval t := ⟨t, ha⟩
  simpa only [prefixCount, prefixSet, ite_eq_left hex, Nat.mul_one] using
    D.deadline_prefix hplusheight hminusheight hL v a

theorem exists_deadline_matching (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (h : D.MBase v → ℚ)
    (hle : ∀ b, h b ≤ D.mainBaseline b)
    (hcover : ∀ (t : D.TestAt v) (a : ℚ), a ∈ D.testInterval t →
      D.d ≤ coverageCount h D.mainBaseline a) :
    ∃ e : D.MBase v ≃ D.MBase v, ∀ b, h b ≤ D.deadline (e b) := by
  classical
  apply exists_equiv_of_prefix_dominance h D.deadline rfl
  intro a
  rw [D.deadline_prefix hplusheight hminusheight hL,
    completion_prefix_identity h D.mainBaseline hle]
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht, Nat.mul_one]
    obtain ⟨t, ht⟩ := ht
    exact Nat.add_le_add_left (hcover t a ht) _
  · rw [ite_eq_right ht, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_add_right _ _

end BinPackingGap.InventoryData

namespace BinPackingGap.LocalResourceAllocation

open UniformTree

def oppositeTree {d : ℕ} (T : CompetingTrees d) : Bool → UniformTree
  | false => T.plus
  | true => T.minus

def oppositeMarking {d : ℕ} (T : CompetingTrees d) :
    (selected : Bool) → Finset (oppositeTree T selected).Node
  | false => T.markingPlus
  | true => T.markingMinus

abbrev OppositeMarked {d : ℕ} (T : CompetingTrees d) (selected : Bool) :=
  ↥(oppositeMarking T selected)

theorem opposite_height {d : ℕ} (T : CompetingTrees d) (selected : Bool) :
    (oppositeTree T selected).height = T.height := by
  cases selected
  · exact T.plus_height
  · exact T.minus_height

theorem opposite_depth_pos {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (a : OppositeMarked T selected) : 0 < depth a.val := by
  cases selected
  · exact T.markingPlus_depth_pos a.val a.property
  · exact T.markingMinus_depth_pos a.val a.property

theorem opposite_quota {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (ell : ℕ) (hlo : 1 ≤ ell) (hhi : ell ≤ T.height) :
    ((oppositeMarking T selected).filter (fun node => depth node = ell)).card ≤
      T.quota ell := by
  cases selected
  · exact T.plus_quota ell hlo hhi
  · exact T.minus_quota ell hlo hhi

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

def markedDepth (selected : Bool) (a : OppositeMarked T selected) : (D).Depth :=
  ⟨depth a.val, Finset.mem_Icc.mpr
    ⟨opposite_depth_pos T selected a,
      (depth_le_height a.val).trans_eq (opposite_height T selected)⟩⟩

def markedByDepth (selected : Bool) : OppositeMarked T selected ↪
    Σ ell : (D).Depth,
      ↥((oppositeMarking T selected).filter (fun node => depth node = ell.val)) := by
  classical
  refine ⟨fun a => ⟨markedDepth G T R k selected a,
    ⟨a.val, Finset.mem_filter.mpr ⟨a.property, rfl⟩⟩⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z => z.2.val) hab

def markedResource (selected : Bool) : OppositeMarked T selected ↪ (D).PositiveLocal := by
  classical
  exact (markedByDepth G T R k selected).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl (D).Depth) (fun ell =>
      (Finset.equivFin
        ((oppositeMarking T selected).filter (fun node => depth node = ell.val))).toEmbedding.trans
        (Fin.castLEEmb (opposite_quota T selected ell.val
          (Finset.mem_Icc.mp ell.property).1 (Finset.mem_Icc.mp ell.property).2))))

@[simp] theorem markedResource_depth (selected : Bool) (a : OppositeMarked T selected) :
    (markedResource G T R k selected a).1.val = depth a.val := rfl

def markedRow (v : G.Vertex) :
    (selected : Bool) → OppositeMarked T selected → (D).MBase v
  | false, a => .inl (.inl (a.val, ⟨0, hd⟩))
  | true, a => .inl (.inr (.inl (a.val, ⟨0, hd⟩)))

theorem markedRow_injective (v : G.Vertex) (selected : Bool) :
    Function.Injective (markedRow G T hd R k v selected) := by
  cases selected
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hab))
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hab)))

theorem fundedRoot_ne_markedRow (v : G.Vertex) (selected : Bool) (j : Fin d)
    (a : OppositeMarked T selected) :
    (D).fundedRoot selected j ≠ markedRow G T hd R k v selected a := by
  cases selected <;> intro h <;> cases Sum.inl.inj h

def zeroResource (v : G.Vertex) : Fin d ↪ (D).DMAt v := by
  clear hd
  have hstock : d ≤ (D).t - (D).P := by
    have h := (D).two_mul_d_le_t_sub_P
    change 2 * d ≤ (D).t - (D).P at h
    omega
  refine ⟨fun j => .inr (.inl (Fin.castLE hstock j)), ?_⟩
  intro a b hab
  exact Fin.castLE_injective hstock (Sum.inl.inj (Sum.inr.inj hab))

@[simp] theorem zeroResource_local_length (v : G.Vertex) (j : Fin d) :
    (D).localLength (.inl (zeroResource G T R k v j)) = 0 := rfl

def seedRows (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).MBase v := by
  refine ⟨Sum.elim ((D).fundedRoot selected) (markedRow G T hd R k v selected), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((D).fundedRoot_injective v selected hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected a b hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected b a hab.symm)
  · exact congrArg Sum.inr (markedRow_injective G T hd R k v selected hab)

def seedResources (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).DMAt v := by
  refine ⟨Sum.elim (zeroResource G T R k v)
    (fun a => .inl (markedResource G T R k selected a)), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((zeroResource G T R k v).injective hab)
  · have hbad : Sum.inr _ = Sum.inl _ := hab
    cases hbad
  · have hbad : Sum.inl _ = Sum.inr _ := hab
    cases hbad
  · exact congrArg Sum.inr ((markedResource G T R k selected).injective (Sum.inl.inj hab))

theorem exists_localEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).DMAt v,
      ∀ s : Fin d ⊕ OppositeMarked T selected,
        e (seedRows G T hd R k v selected s) = seedResources G T R k v selected s := by
  let : Fintype ((D).MBase v) := by
    dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
      InventoryData.ofCompetingTrees]
    infer_instance
  let : Fintype ((D).DMAt v) := by
    dsimp [InventoryData.DMAt, InventoryData.PositiveLocal, InventoryData.ZeroLocalAt,
      InventoryData.Depth, InventoryData.JobCopy, InventoryData.ofCompetingTrees]
    infer_instance
  apply PartialAllocation.exists_equiv_extending_embeddings
    (seedRows G T hd R k v selected) (seedResources G T R k v selected)
  exact ((D).card_mBase v).trans ((D).card_dmAt v).symm

def localEquiv (v : G.Vertex) (selected : Bool) : (D).MBase v ≃ (D).DMAt v :=
  Classical.choose (exists_localEquiv G T hd R k v selected)

theorem localEquiv_seed (v : G.Vertex) (selected : Bool)
    (s : Fin d ⊕ OppositeMarked T selected) :
    localEquiv G T hd R k v selected (seedRows G T hd R k v selected s) =
      seedResources G T R k v selected s :=
  Classical.choose_spec (exists_localEquiv G T hd R k v selected) s

theorem localEquiv_fundedRoot (v : G.Vertex) (selected : Bool) (j : Fin d) :
    localEquiv G T hd R k v selected ((D).fundedRoot selected j) =
      zeroResource G T R k v j :=
  localEquiv_seed G T hd R k v selected (.inl j)

theorem localEquiv_markedRow (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    localEquiv G T hd R k v selected (markedRow G T hd R k v selected a) =
      .inl (markedResource G T R k selected a) :=
  localEquiv_seed G T hd R k v selected (.inr a)

theorem fundedRoot_local_zero (v : G.Vertex) (selected : Bool) (j : Fin d) :
    (D).localLength (.inl (localEquiv G T hd R k v selected ((D).fundedRoot selected j))) =
      0 := by
  rw [localEquiv_fundedRoot, zeroResource_local_length]

theorem markedRow_local_length (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    (D).localLength (.inl (localEquiv G T hd R k v selected
      (markedRow G T hd R k v selected a))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth a.val) := by
  rw [localEquiv_markedRow]
  change Geometry.lambda G.edges.length R (D).geometryBound
    (markedResource G T R k selected a).1.val = _
  rw [markedResource_depth]

theorem plusMarked_local_length (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    (D).localLength (.inl (localEquiv G T hd R k v false
      (.inl (.inl (node, ⟨0, hd⟩))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v false ⟨node, hnode⟩

theorem minusMarked_local_length (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    (D).localLength (.inl (localEquiv G T hd R k v true
      (.inl (.inr (.inl (node, ⟨0, hd⟩)))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v true ⟨node, hnode⟩

end BinPackingGap.LocalResourceAllocation

namespace BinPackingGap.LocalCompletionCoverage

open InventoryData IntervalCoverage

private theorem card_le_coverage {ι κ : Type*} [Fintype ι]
    (h baseline : ι → ℚ) (a : ℚ) (s : Finset κ) (f : κ → ι)
    (hf : Function.Injective f)
    (hc : ∀ x ∈ s, h (f x) ≤ a ∧ a < baseline (f x)) :
    s.card ≤ coverageCount h baseline a := by
  classical
  exact Finset.card_le_card_of_injOn f
    (fun x hx => (mem_coverageSet h baseline a (f x)).mpr (hc x hx))
    (fun _ _ _ _ hxy => hf hxy)

private theorem nodeInterval_subset_root {U : UniformTree} (node : U.Node)
    (m R B : ℕ) (side : TreeGeometry.Side) (hB : U.branchBound ≤ B)
    {a : ℚ}
    (ha : a ∈ Set.Ico (TreeGeometry.left m R B side node.val)
      (TreeGeometry.right m R B side node.val)) :
    a ∈ Set.Ico (TreeGeometry.rootOffset side) (TreeGeometry.rootOffset side + 1) := by
  have he := TreeGeometry.prefix_endpoints m R B side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hB)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at he
  exact ⟨he.1.trans ha.1, ha.2.trans_le he.2⟩

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

local instance mainFintype (v : G.Vertex) : Fintype ((D).MBase v) := by
  dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
    InventoryData.ofCompetingTrees]
  infer_instance

def localCompletion (v : G.Vertex) (selected : Bool) (b : (D).MBase v) : ℚ :=
  (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
    (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))

theorem localCompletion_le_baseline (v : G.Vertex) (selected : Bool) (b : (D).MBase v) :
    localCompletion G T hd R k v selected b ≤ (D).mainBaseline b := by
  have hg := (D).stateMainLength_nonneg selected b
  have hl := (D).localLength_nonneg
    (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))
  have hdelta := Geometry.delta_nonneg G.edges.length R (D).geometryBound (D).L
  have hshort : (0 : ℚ) ≤
      if (D).rowShort ((D).stateMainRow v selected b) then
        Geometry.delta G.edges.length R (D).geometryBound (D).L else 0 := by
    split_ifs
    · exact hdelta
    · exact le_rfl
  have hbase := (D).stateMainRow_baseline v selected b
  unfold localCompletion rowCoordinate
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hbase]
  linarith

private theorem fundedRoot_covers (v : G.Vertex) (selected : Bool) (j : Fin d)
    {a : ℚ} (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    localCompletion G T hd R k v selected ((D).fundedRoot selected j) ≤ a ∧
      a < (D).mainBaseline ((D).fundedRoot (v := v) selected j) := by
  have hzero := LocalResourceAllocation.fundedRoot_local_zero G T hd R k v selected j
  have hglobal := (D).stateMainLength_fundedRoot (v := v) selected j
  unfold localCompletion
  rw [hzero, hglobal]
  cases selected <;>
    norm_num [fundedRoot, stateMainRow, stateRowEquiv, rowCoordinate, rowBaseline,
      rowShort, mainBaseline, treeBaseline, UniformTree.root, TreeGeometry.right_nil,
      TreeGeometry.rootOffset] at ha ⊢ <;> exact ha

private theorem fundedRoot_coverage (v : G.Vertex) (selected : Bool) {a : ℚ}
    (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v selected)
    (D).mainBaseline a (Finset.univ : Finset (Fin d)) ((D).fundedRoot selected)
    ((D).fundedRoot_injective v selected)
    (fun j _ => fundedRoot_covers G T hd R k v selected j ha)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

private theorem plusMarked_completion_le (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    localCompletion G T hd R k v false (.inl (.inl (node, ⟨0, hd⟩))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val := by
  have hlocal := LocalResourceAllocation.plusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg false
    (.inl (.inl (node, ⟨0, hd⟩))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingPlus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v false (.inl (.inl (node, ⟨0, hd⟩)))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

private theorem minusMarked_completion_le (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    localCompletion G T hd R k v true (.inl (.inr (.inl (node, ⟨0, hd⟩)))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val := by
  have hlocal := LocalResourceAllocation.minusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg true
    (.inl (.inr (.inl (node, ⟨0, hd⟩)))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingMinus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v true (.inl (.inr (.inl (node, ⟨0, hd⟩))))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

private theorem plusMarked_coverage (v : G.Vertex) (leaf : (D).PlusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inl leaf : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  apply (T.plus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v false) (D).mainBaseline a
    (T.markingPlus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inl (node, ⟨0, hd⟩)))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hxy))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .plus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).plus_branch_le_geometryBound)
    exact ⟨(plusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

private theorem minusMarked_coverage (v : G.Vertex) (leaf : (D).MinusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inl leaf) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v true) (D).mainBaseline a := by
  classical
  apply (T.minus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v true) (D).mainBaseline a
    (T.markingMinus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inr (.inl (node, ⟨0, hd⟩))))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hxy)))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .minus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).minus_branch_le_geometryBound)
    exact ⟨(minusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

private theorem shortJob_coverage (v : G.Vertex) (job : (D).IncidencePosition v) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inr job) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v false)
    (D).mainBaseline a (Finset.univ : Finset (Fin d))
    (fun j => .inr (job, j))
    (by intro i j hij; exact congrArg Prod.snd (Sum.inr.inj hij)) (by
      intro j _
      have hl := (D).localLength_nonneg
        (.inl (LocalResourceAllocation.localEquiv G T hd R k v false (.inr (job, j))))
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
        Geometry.delta G.edges.length R (D).geometryBound (D).L - 0 -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v false
          (.inr (job, j)))) ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job)
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
          Geometry.delta G.edges.length R (D).geometryBound (D).L ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job) at ha
      exact ⟨by linarith [ha.1], ha.2⟩)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem localCompletion_coverage (v : G.Vertex) (selected : Bool)
    (test : (D).TestAt v) (a : ℚ) (ha : a ∈ (D).testInterval test) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  cases selected
  · rcases test with leaf | leaf | job
    · exact plusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v false
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .minus
        (D).minus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact shortJob_coverage G T hd R k v job ha
  · rcases test with leaf | leaf | job
    · apply fundedRoot_coverage G T hd R k v true
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .plus
        (D).plus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact minusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v true
      have hj := Geometry.closedJobCell_bounds
        (Geometry.jobTestInterval_subset_closedJobCell G.edges.length R (D).geometryBound
          (D).L ((D).incidencePosition job) ha)
      exact ⟨by dsimp; linarith [hj.1], hj.2⟩

theorem exists_anchorEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).MBase v, ∀ b,
      (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b)) ≤
          (D).deadline (e b) := by
  exact (D).exists_deadline_matching T.plus_height T.minus_height T.height_pos v
    (localCompletion G T hd R k v selected)
    (localCompletion_le_baseline G T hd R k v selected)
    (localCompletion_coverage G T hd R k v selected)

end BinPackingGap.LocalCompletionCoverage

end

end OAI
