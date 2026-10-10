import OAI.Computability.BinPacking.Packing.PackingSelections
import OAI.Computability.BinPacking.Trees.TestGeometry

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def treeBaseline : D.TreeRow → ℚ
  | .inl (node, _) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def rowBaseline {v : D.Vertex} : D.RowAt v → ℚ
  | .inl r => D.treeBaseline r
  | .inr (_, j) => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def mainBaseline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeBaseline r
  | .inr j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def treeDeadline : D.TreeRow → ℚ
  | .inl (node, _) =>
      if node.val ∈ D.plus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      if node.val ∈ D.minus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def deadline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeDeadline r
  | .inr j => Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)

def rowCoordinate {v : D.Vertex} (r : D.RowAt v) : ℚ :=
  D.rowBaseline r - if D.rowShort r then
    Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0

def anchorCoordinate {v : D.Vertex} : D.AnchorAt v → ℚ
  | .inl z => -D.deadline z
  | .inr j => -Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) -
      Geometry.beta D.graph.edges.length D.R (D.jobPosition j).1

def globalLength : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => if one then 1 else 0
  | ⟨.um one, _⟩ => if one then 1 else 0
  | ⟨.edge _ _, _⟩ => 0

def globalCoordinate : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => -(if one then 1 else 0)
  | ⟨.um one, _⟩ => -(if one then 1 else 0)
  | ⟨.edge e permit, _⟩ => Geometry.beta D.graph.edges.length D.R e +
      if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L

def localLength {v : D.Vertex} : D.LocalAt v → ℚ
  | .inl (.inl ⟨ell, _⟩) =>
      Geometry.lambda D.graph.edges.length D.R D.geometryBound ell.val
  | _ => 0

def localCoordinate {v : D.Vertex} (i : D.LocalAt v) : ℚ := -D.localLength i

def itemCoordinate : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowCoordinate r
  | ⟨.anchor, ⟨_, a⟩⟩ => D.anchorCoordinate a
  | ⟨.«global», u⟩ => D.globalCoordinate u
  | ⟨.«local», ⟨_, l⟩⟩ => D.localCoordinate l
  | ⟨.flag, _⟩ => 0

theorem mainBaseline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.mainBaseline (D.designated q) = D.testRight q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r <;> rfl

theorem deadline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.deadline (D.designated q) = D.testLeft q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · rfl

theorem globalLength_nonneg (u : D.GlobalCopy) : 0 ≤ D.globalLength u := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

theorem globalLength_le_one (u : D.GlobalCopy) : D.globalLength u ≤ 1 := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

private theorem node_endpoint_bounds {T : UniformTree} (node : T.Node)
    (side : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    (0 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) ∧
    (0 ≤ TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) := by
  have hroot := TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hT)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at hroot
  have hwidth := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound side node.val
  cases side <;> simp only [TreeGeometry.rootOffset] at hroot <;>
    constructor <;> constructor <;> linarith [hroot.1, hroot.2]

theorem treeBaseline_bounds (r : D.TreeRow) :
    0 ≤ D.treeBaseline r ∧ D.treeBaseline r ≤ 5 := by
  rcases r with p | p | padding
  · exact (D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound).2
  · exact (D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound).2
  · norm_num [treeBaseline]

theorem treeDeadline_bounds (r : D.TreeRow) :
    0 ≤ D.treeDeadline r ∧ D.treeDeadline r ≤ 5 := by
  rcases r with p | p | padding
  · have h := D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · have h := D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · norm_num [treeDeadline]

private theorem jobBaseline_bounds (p : D.Position) :
    0 ≤ Geometry.baseline D.graph.edges.length D.R p ∧
      Geometry.baseline D.graph.edges.length D.R p ≤ 5 := by
  have h := Geometry.baseline_range D.graph.edges.length D.R p
  constructor <;> linarith [h.1, h.2]

theorem rowBaseline_bounds {v : D.Vertex} (r : D.RowAt v) :
    0 ≤ D.rowBaseline r ∧ D.rowBaseline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeBaseline_bounds tree
  · exact D.jobBaseline_bounds (D.jobPosition job.2)

theorem mainBaseline_bounds {v : D.Vertex} (r : D.MBase v) :
    0 ≤ D.mainBaseline r ∧ D.mainBaseline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeBaseline_bounds tree
  · exact D.jobBaseline_bounds (D.jobPosition job)

theorem deadline_bounds {v : D.Vertex} (r : D.MBase v) :
    0 ≤ D.deadline r ∧ D.deadline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeDeadline_bounds tree
  · have hl := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hu := Geometry.jobLeft_lt_baseline D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hb := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.jobPosition job)
    change 0 ≤ Geometry.jobLeft _ _ _ _ _ ∧ Geometry.jobLeft _ _ _ _ _ ≤ 5
    constructor <;> linarith

theorem rowCoordinate_bounds {v : D.Vertex} (r : D.RowAt v) :
    0 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5 := by
  rcases r with tree | ⟨short, job⟩
  · simpa only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
      sub_zero] using D.treeBaseline_bounds tree
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition job)
    have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
    have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
    have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
    cases short <;>
      simp only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
        ite_true, sub_zero] <;>
      constructor <;> linarith [hb.1, hb.2]

theorem anchorCoordinate_bounds {v : D.Vertex} (a : D.AnchorAt v) :
    -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 0 := by
  rcases a with deadline | key
  · have h := D.deadline_bounds deadline
    change -5 ≤ -D.deadline deadline ∧ -D.deadline deadline ≤ 0
    constructor <;> linarith [h.1, h.2]
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition key)
    have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R (D.jobPosition key).1
    have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R (D.jobPosition key).1
    dsimp only [anchorCoordinate]
    constructor <;> linarith [hb.1, hb.2]

theorem globalCoordinate_bounds (u : D.GlobalCopy) :
    -1 ≤ D.globalCoordinate u ∧ D.globalCoordinate u ≤ 1 := by
  rcases u with ⟨species, copy⟩
  cases species with
  | up one => cases one <;> norm_num [globalCoordinate]
  | um one => cases one <;> norm_num [globalCoordinate]
  | edge edge permit =>
      have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R edge
      have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R edge
      have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
      have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
      have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
      cases permit <;>
        simp only [globalCoordinate, Bool.false_eq_true, ite_false, ite_true, add_zero] <;>
        constructor <;> linarith

theorem localLength_nonneg {v : D.Vertex} (i : D.LocalAt v) : 0 ≤ D.localLength i := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound ell.val
  · exact le_rfl
  · exact le_rfl

theorem localLength_le_lambda_one {v : D.Vertex} (i : D.LocalAt v) :
    D.localLength i ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_antitone D.graph.edges.length D.R D.geometryBound
      (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1

theorem localLength_le_one {v : D.Vertex} (i : D.LocalAt v) : D.localLength i ≤ 1 :=
  (D.localLength_le_lambda_one i).trans
    (Geometry.lambda_le_one D.graph.edges.length D.R D.geometryBound 1)

theorem localCoordinate_bounds {v : D.Vertex} (i : D.LocalAt v) :
    -1 ≤ D.localCoordinate i ∧ D.localCoordinate i ≤ 0 := by
  have h0 := D.localLength_nonneg i
  have h1 := D.localLength_le_one i
  unfold localCoordinate
  constructor <;> linarith

theorem itemCoordinate_bounds (i : D.Item) :
    -5 ≤ D.itemCoordinate i ∧ D.itemCoordinate i ≤ 5 := by
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
      rcases i with ⟨v, r⟩
      have h := D.rowCoordinate_bounds r
      change -5 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5
      exact ⟨by linarith [h.1], h.2⟩
  | anchor =>
      rcases i with ⟨v, a⟩
      have h := D.anchorCoordinate_bounds a
      change -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 5
      exact ⟨h.1, by linarith [h.2]⟩
  | «global» =>
      have h := D.globalCoordinate_bounds i
      change -5 ≤ D.globalCoordinate i ∧ D.globalCoordinate i ≤ 5
      constructor <;> linarith [h.1, h.2]
  | «local» =>
      rcases i with ⟨v, l⟩
      have h := D.localCoordinate_bounds l
      change -5 ≤ D.localCoordinate l ∧ D.localCoordinate l ≤ 5
      constructor <;> linarith [h.1, h.2]
  | flag => norm_num [itemCoordinate]

theorem itemCoordinate_abs_le_six (i : D.Item) : |D.itemCoordinate i| ≤ 6 := by
  have h := D.itemCoordinate_bounds i
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

def stateRowEquiv (v : D.Vertex) (selected : Bool) : D.LocalBin v ≃ D.RowAt v where
  toFun
    | .inl (.inl t) => .inl t
    | .inl (.inr j) => .inr (!selected, j)
    | .inr j => .inr (selected, j)
  invFun
    | .inl t => .inl (.inl t)
    | .inr (short, j) => if short = selected then .inr j else .inl (.inr j)
  left_inv i := by
    rcases i with (t | j) | j <;> cases selected <;> simp
  right_inv r := by
    rcases r with t | ⟨b, j⟩
    · rfl
    · cases b <;> cases selected <;> simp

@[simp] theorem stateRowEquiv_tree (v : D.Vertex) (selected : Bool) (t : D.TreeRow) :
    D.stateRowEquiv v selected (.inl (.inl t)) = .inl t := rfl

@[simp] theorem stateRowEquiv_mainJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inl (.inr j)) = .inr (!selected, j) := rfl

@[simp] theorem stateRowEquiv_edgeJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inr j) = .inr (selected, j) := rfl

def stateMainRow (v : D.Vertex) (selected : Bool) (b : D.MBase v) : D.RowAt v :=
  D.stateRowEquiv v selected (.inl b)

theorem stateMainRow_injective (v : D.Vertex) (selected : Bool) :
    Function.Injective (D.stateMainRow v selected) := by
  intro b c h
  exact Sum.inl.inj ((D.stateRowEquiv v selected).injective h)

@[simp] theorem stateMainRow_baseline (v : D.Vertex) (selected : Bool) (b : D.MBase v) :
    D.rowBaseline (D.stateMainRow v selected b) = D.mainBaseline b := by
  rcases b with t | j <;> rfl

def stateFlagSpecies {v : D.Vertex} : D.LocalBin v → FlagSpecies
  | .inl (.inl _) => .tree
  | .inl (.inr _) => .main
  | .inr _ => .edge

def stateMainGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.MBase v → GlobalSpecies D.graph
  | .inl (.inl (node, _)) => .up (selected && decide (node = D.plus.root))
  | .inl (.inr (.inl (node, _))) => .um (!selected && decide (node = D.minus.root))
  | .inl (.inr (.inr _)) => .up false
  | .inr _ => .up false

def stateGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.LocalBin v → GlobalSpecies D.graph
  | .inl b => D.stateMainGlobalSpecies selected b
  | .inr j => .edge (D.jobPosition j).1 (!selected)

def globalSpeciesLength : GlobalSpecies D.graph → ℚ
  | .up one => if one then 1 else 0
  | .um one => if one then 1 else 0
  | .edge _ _ => 0

theorem globalLength_eq_species (u : D.GlobalCopy) :
    D.globalLength u = D.globalSpeciesLength u.1 := by
  rcases u with ⟨s, i⟩
  cases s <;> rfl

def stateMainLength {v : D.Vertex} (selected : Bool) (b : D.MBase v) : ℚ :=
  D.globalSpeciesLength (D.stateMainGlobalSpecies selected b)

theorem stateMainLength_nonneg {v : D.Vertex} (selected : Bool) (b : D.MBase v) :
    0 ≤ D.stateMainLength selected b := by
  rcases b with (⟨p, i⟩ | ⟨m, i⟩ | i) | j
  all_goals simp only [stateMainLength, stateMainGlobalSpecies, globalSpeciesLength]
  all_goals split_ifs <;> norm_num

theorem stateMainLength_le_one {v : D.Vertex} (selected : Bool) (b : D.MBase v) :
    D.stateMainLength selected b ≤ 1 := by
  rcases b with (⟨p, i⟩ | ⟨m, i⟩ | i) | j
  all_goals simp only [stateMainLength, stateMainGlobalSpecies, globalSpeciesLength]
  all_goals split_ifs <;> norm_num

def fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) : D.MBase v :=
  if selected then .inl (.inl (D.plus.root, j))
  else .inl (.inr (.inl (D.minus.root, j)))

theorem fundedRoot_injective (v : D.Vertex) (selected : Bool) :
    Function.Injective (D.fundedRoot (v := v) selected) := by
  intro i j h
  cases selected <;> simpa [fundedRoot] using h

@[simp] theorem stateMainLength_fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) :
    D.stateMainLength selected (D.fundedRoot (v := v) selected j) = 1 := by
  cases selected <;> simp [fundedRoot, stateMainLength, stateMainGlobalSpecies,
    globalSpeciesLength]

abbrev PhysicalBins := Σ v : D.Vertex, D.LocalBin v

theorem card_physicalBins : Fintype.card D.PhysicalBins = D.B := by
  simp only [PhysicalBins, Fintype.card_sigma, D.card_localBin, B]

structure LocalState (v : D.Vertex) (selected : Bool) where
  localEquiv : D.MBase v ≃ D.DMAt v
  anchorEquiv : D.MBase v ≃ D.MBase v
  completion_le_deadline : ∀ b,
    D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
      D.localLength (.inl (localEquiv b)) ≤ D.deadline (anchorEquiv b)

namespace LocalState

variable {D} {v : D.Vertex} {selected : Bool} (S : D.LocalState v selected)

def anchorAtEquiv : D.LocalBin v ≃ D.AnchorAt v :=
  Equiv.sumCongr S.anchorEquiv (Equiv.refl _)

def localAtEquiv : D.LocalBin v ≃ D.LocalAt v :=
  Equiv.sumCongr S.localEquiv (Equiv.refl _)

@[simp] theorem anchorAtEquiv_main (b : D.MBase v) :
    S.anchorAtEquiv (.inl b) = .inl (S.anchorEquiv b) := rfl

@[simp] theorem anchorAtEquiv_edge (j : D.JobCopy v) :
    S.anchorAtEquiv (.inr j) = .inr j := rfl

@[simp] theorem localAtEquiv_main (b : D.MBase v) :
    S.localAtEquiv (.inl b) = .inl (S.localEquiv b) := rfl

@[simp] theorem localAtEquiv_edge (j : D.JobCopy v) :
    S.localAtEquiv (.inr j) = .inr j := rfl

end LocalState

end BinPackingGap.InventoryData

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleBaseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.rowBaseline (rowCopy p e t).2

def tupleShort (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Bool := D.rowShort (rowCopy p e t).2

def tupleGlobalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.globalLength (globalCopy p e t)

def tupleLocalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.localLength (localCopy p e t).2

def tupleFinish (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ :=
  completion (tupleBaseline p e t) (tupleShort p e t)
    (tupleGlobalLength p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)

def tupleClosedInterval (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Set ℚ :=
  Set.Icc (tupleFinish p e t) (tupleBaseline p e t)

def tupleCoveringInterval (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Set ℚ :=
  Set.Ico (tupleFinish p e t) (tupleBaseline p e t)

def tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t

@[simp] theorem mem_tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) (t : p.TableBin (subclass e)) :
    t ∈ tupleCovering p e v a ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t := by
  classical
  simp [tupleCovering, and_assoc]

theorem tupleGlobalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleGlobalLength p e t :=
  D.globalLength_nonneg _

theorem tupleGlobalLength_le_one (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleGlobalLength p e t ≤ 1 :=
  D.globalLength_le_one _

theorem tupleGlobalLength_eq_of_unit_false (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : D.globalUnit (globalCopy p e t) = false) :
    tupleGlobalLength p e t = 0 := by
  have h : D.globalLength (globalCopy p e t) =
      if D.globalUnit (globalCopy p e t) then 1 else 0 := by
    rcases globalCopy p e t with ⟨s, i⟩
    cases s <;> rfl
  simpa only [tupleGlobalLength, hu, Bool.false_eq_true, ↓reduceIte] using h

private theorem localLength_nonneg {v : D.Vertex} (l : D.LocalAt v) : 0 ≤ D.localLength l := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_nonneg _ _ _ _
  · rfl
  · rfl

private theorem localLength_le_first {v : D.Vertex} (l : D.LocalAt v) :
    D.localLength l ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_antitone _ _ _ (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg _ _ _ _
  · exact Geometry.lambda_nonneg _ _ _ _

theorem tupleLocalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleLocalLength p e t :=
  localLength_nonneg _

theorem tupleLocalLength_le_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    tupleLocalLength p e t ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 :=
  localLength_le_first _

theorem tupleLocalLength_eq_zero_of_not_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v)
    (hnot : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v) :
    tupleLocalLength p e t = 0 := by
  rcases hc : localCopy p e t with ⟨w, ((i | z) | g)⟩
  · have hw : w = v := by simpa only [hc] using good_local_vertex p e v t ht
    subst w
    exfalso
    apply hnot
    apply (mem_positiveLocalResources e v _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«local»]
    exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hc.symm
  · unfold tupleLocalLength
    rw [hc]
    rfl
  · unfold tupleLocalLength
    rw [hc]
    rfl

theorem tupleFinish_le_baseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleFinish p e t ≤ tupleBaseline p e t :=
  completion_le_baseline _ _ _ _ _ (tupleGlobalLength_nonneg p e t)
    (tupleLocalLength_nonneg p e t) (Geometry.delta_nonneg _ _ _ _)

theorem selected_localLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalLength p e t =
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  unfold tupleLocalLength tupleLocalDepth
  rw [hi]
  rfl

theorem selected_interval_length (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu, selected_localLength p e v t ht]
  exact completion_zero_global_length_le _ _ _ _ (Geometry.delta_nonneg _ _ _ _)

theorem selected_interval_length_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu]
  apply le_trans (completion_zero_global_length_le
    (tupleBaseline p e t) (tupleShort p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)
    (Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L))
  exact add_le_add (tupleLocalLength_le_first p e t) le_rfl

end PackingCounts
end BinPackingGap

end

end OAI
