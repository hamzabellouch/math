import Mathlib
import OAI.LinearAlgebra.MatrixFields.Parameters.GroupSelectionParameters

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def splitCoordinateWeight (parents : List Shape) (data : List ℤ)
    (s : Shape) (i : Fin 3) (k : ℕ) : ℝ :=
  (weight (assigned (splitKeys parents) data (s, i, min k (s i - k))) : ℝ)

def splitPotential (parents : List Shape) (data : List ℤ)
    (s : Shape) (i : Fin 3) (k : ℕ) : ℝ :=
  Real.log (splitCoordinateWeight parents data s i k)

def splitNormalizer (parents : List Shape) (data : List ℤ) (s : Shape) : ℝ :=
  (((below s).map (splitWeight parents data s)).sum : ℚ)

def splitLogNormalizer (parents : List Shape) (data : List ℤ) (s : Shape) : ℝ :=
  Real.log (splitNormalizer parents data s)

theorem splitCoordinateWeight_pos (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (i : Fin 3) (k : ℕ) :
    0 < splitCoordinateWeight parents data s i k := by
  apply Rat.cast_pos.mpr
  exact weight_positive_of_argument_bound _ (assigned_argument_bound _ data hd _)

theorem splitNormalizer_pos (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (hne : below s ≠ []) :
    0 < splitNormalizer parents data s := by
  apply Rat.cast_pos.mpr
  exact list_sum_map_positive _ _ hne (fun u _ => splitWeight_positive parents data hd s u)

theorem splitWeight_log (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) :
    Real.log (splitWeight parents data s u : ℝ) =
      ∑ i : Fin 3, splitPotential parents data s i (u i) := by
  have hweight (i : Fin 3) : (weight (splitSignature parents data s u i) : ℝ) ≠ 0 :=
    ne_of_gt (splitCoordinateWeight_pos parents data hd s i (u i))
  rw [splitWeight, Rat.cast_prod, Real.log_prod (fun index _ => hweight index)]
  rfl

theorem splitLaw_log (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s) :
    Real.log (splitLaw parents data s u : ℝ) =
      (∑ i : Fin 3, splitPotential parents data s i (u i)) -
        splitLogNormalizer parents data s := by
  have hweight : (splitWeight parents data s u : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (splitWeight_positive parents data hd s u)
  have hne : below s ≠ [] := by
    intro he
    simp only [he, List.not_mem_nil] at hu
  have hnormal := ne_of_gt (splitNormalizer_pos parents data hd s hne)
  rw [splitLaw, ite_eq_left hu, Rat.cast_div]
  change Real.log ((splitWeight parents data s u : ℝ) / splitNormalizer parents data s) = _
  rw [Real.log_div hweight hnormal, splitWeight_log parents data hd]
  rfl

theorem splitLaw_positive_iff (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) :
    0 < (splitLaw parents data s u : ℝ) ↔ u ∈ below s := by
  constructor
  · intro hp
    by_contra hu
    rw [splitLaw_outside_support parents data s u hu] at hp
    norm_num at hp
  · intro hu
    exact_mod_cast splitLaw_positive parents data hd s u hu

def physicalPotential (parents : List Shape) (data : List ℤ) (s : Shape)
    (phi : Placement) (i : Fin 3) (k : Fin 17) : ℝ :=
  splitPotential parents data s (phi.symm i) k.val

theorem splitLaw_log_physical (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s)
    (hb : ShapeBounded u) (phi : Placement) :
    Real.log (splitLaw parents data s u : ℝ) =
      physicalPotential parents data s phi 0 (JointPopulation.shapeSide 0 (encodePhysicalShape phi u hb)) +
      physicalPotential parents data s phi 1 (JointPopulation.shapeSide 1 (encodePhysicalShape phi u hb)) +
      physicalPotential parents data s phi 2 (JointPopulation.shapeSide 2 (encodePhysicalShape phi u hb)) -
        splitLogNormalizer parents data s := by
  rw [splitLaw_log parents data hd s u hu]
  have hsum : (∑ i : Fin 3, splitPotential parents data s i (u i)) =
      ∑ i : Fin 3, physicalPotential parents data s phi i
        (JointPopulation.shapeSide i (encodePhysicalShape phi u hb)) := by
    simp only [physicalPotential, encodePhysicalShape_side]
    exact (phi.symm.sum_comp (fun i => splitPotential parents data s i (u i))).symm
  rw [hsum, Fin.sum_univ_three]

theorem placedLaw_positive_has_branch {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw w).mass u) :
    ∃ b : w.1.Branch, branchShape w b = u := by
  by_contra hn
  have hz : (placedLaw w).mass u = 0 := by
    rw [placedLaw_mass]
    apply Finset.sum_eq_zero
    intro b _
    exact ite_eq_right (fun hb => hn ⟨b, hb⟩)
  rw [hz] at hu
  exact lt_irrefl 0 hu

theorem placedLaw_stageA_branch_log {K : ℕ} (h : InitialPositive K)
    (phi : Placement) (b : ASplit h) :
    Real.log ((placedLaw (Work.stageA h, phi)).mass (branchShape (Work.stageA h, phi) b)) =
      physicalPotential positiveInitial tableP (initialShape h.val) phi 0
        (JointPopulation.shapeSide 0 (branchShape (Work.stageA h, phi) b)) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 1
        (JointPopulation.shapeSide 1 (branchShape (Work.stageA h, phi) b)) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 2
        (JointPopulation.shapeSide 2 (branchShape (Work.stageA h, phi) b)) -
      splitLogNormalizer positiveInitial tableP (initialShape h.val) := by
  refine (congrArg Real.log (placedLaw_mass_branch (Work.stageA h, phi) b)).trans ?_
  exact splitLaw_log_physical positiveInitial tableP stageA_table_arguments_bounded
    (initialShape h.val) (aSplit ⟨h, b, false⟩) (aSplit_mem ⟨h, b, false⟩)
    ((Work.stageA h).splitShape_spec b).1 phi

theorem placedLaw_stageB_branch_log {K : ℕ} (h : APositive K)
    (phi : Placement) (b : BSplit h) :
    Real.log ((placedLaw (Work.stageB h, phi)).mass (branchShape (Work.stageB h, phi) b)) =
      physicalPotential positiveSecond tablep (aShape h.val) phi 0
        (JointPopulation.shapeSide 0 (branchShape (Work.stageB h, phi) b)) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 1
        (JointPopulation.shapeSide 1 (branchShape (Work.stageB h, phi) b)) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 2
        (JointPopulation.shapeSide 2 (branchShape (Work.stageB h, phi) b)) -
      splitLogNormalizer positiveSecond tablep (aShape h.val) := by
  refine (congrArg Real.log (placedLaw_mass_branch (Work.stageB h, phi) b)).trans ?_
  exact splitLaw_log_physical positiveSecond tablep stageB_table_arguments_bounded
    (aShape h.val) (bSplit ⟨h, b, false⟩) (bSplit_mem ⟨h, b, false⟩)
    ((Work.stageB h).splitShape_spec b).1 phi

theorem placedLaw_stageA_log {K : ℕ} (h : InitialPositive K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageA h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageA h, phi)).mass u) =
      physicalPotential positiveInitial tableP (initialShape h.val) phi 0 (JointPopulation.shapeSide 0 u) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 1 (JointPopulation.shapeSide 1 u) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 2 (JointPopulation.shapeSide 2 u) -
      splitLogNormalizer positiveInitial tableP (initialShape h.val) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageA h, phi) u hu
  exact placedLaw_stageA_branch_log h phi b

theorem placedLaw_stageB_log {K : ℕ} (h : APositive K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageB h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageB h, phi)).mass u) =
      physicalPotential positiveSecond tablep (aShape h.val) phi 0 (JointPopulation.shapeSide 0 u) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 1 (JointPopulation.shapeSide 1 u) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 2 (JointPopulation.shapeSide 2 u) -
      splitLogNormalizer positiveSecond tablep (aShape h.val) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageB h, phi) u hu
  exact placedLaw_stageB_branch_log h phi b

theorem mem_shapes_of_total (u : Shape) (n : ℕ)
    (h : shapeTotal u = n) : u ∈ shapes n := by
  dsimp [shapeTotal] at h
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨u 0, by omega, u 1, by omega, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · change n - u 0 - u 1 = u 2
    omega

theorem mem_below_iff (s u : Shape) :
    u ∈ below s ↔ shapeTotal u = shapeTotal s / 2 ∧ ∀ i, u i ≤ s i := by
  constructor
  · intro hu
    exact ⟨below_total hu, below_le hu⟩
  · rintro ⟨ht, hle⟩
    apply List.mem_filter.mpr
    refine ⟨mem_shapes_of_total u _ ht, ?_⟩
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
      And.intro (hle 0) (And.intro (hle 1) (hle 2))

theorem splitShape_exhaustive {K : ℕ} (w : Work K)
    (u : Shape) (hu : u ∈ below w.parentShape) :
    ∃ b : w.Branch, w.splitShape b = u := by
  cases w with
  | stageA h =>
      change u ∈ below (initialShape h.val) at hu
      obtain ⟨b, hb⟩ := List.mem_iff_get.mp hu
      exact ⟨b, hb⟩
  | stageB h =>
      change u ∈ below (aShape h.val) at hu
      obtain ⟨b, hb⟩ := List.mem_iff_get.mp hu
      exact ⟨b, hb⟩
  | stageC h =>
      exact stageCAtom_exhaustive _ (bShape_size h.1.val) h.1.property u hu

theorem branchShape_exhaustive {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape)
    (ht : u.1.val + u.2.1.val + u.2.2.val = 2 * w.1.halfLength)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape w.2 w.1.parentShape i) :
    ∃ b : w.1.Branch, branchShape w b = u := by
  let v : Shape := physicalShape w.2.symm (decodeShape u)
  have hvt : shapeTotal v = 2 * w.1.halfLength := by
    dsimp [v]
    rw [physicalShape_total]
    exact ht
  have hvl : ∀ i, v i ≤ w.1.parentShape i := by
    intro i
    simpa only [v, physicalShape, decodeShape, Equiv.symm_symm,
      Equiv.symm_apply_apply] using hle (w.2 i)
  have hv : v ∈ below w.1.parentShape := by
    apply (mem_below_iff _ _).2
    refine ⟨?_, hvl⟩
    rw [hvt, (w.1.parentShape_spec).2]
    omega
  obtain ⟨b, hb⟩ := splitShape_exhaustive w.1 v hv
  refine ⟨b, ?_⟩
  have hd : decodeShape (branchShape w b) = decodeShape u := by
    rw [branchShape, decode_encodePhysicalShape, hb]
    funext i
    simp only [v, physicalShape, Equiv.symm_symm, Equiv.apply_symm_apply]
  apply Prod.ext
  · exact Fin.ext (congrFun hd 0)
  · apply Prod.ext
    · exact Fin.ext (congrFun hd 1)
    · exact Fin.ext (congrFun hd 2)

theorem placedLaw_stageA_positive {K : ℕ} (h : InitialPositive K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 8)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape phi (initialShape h.val) i) :
    0 < (placedLaw (Work.stageA h, phi)).mass u := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageA h, phi) u ht hle
  rw [placedLaw_mass_branch]
  exact_mod_cast stageALaw_positive (initialShape h.val) (aSplit ⟨h, b, false⟩)
    (aSplit_mem ⟨h, b, false⟩)

theorem placedLaw_stageB_positive {K : ℕ} (h : APositive K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 4)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape phi (aShape h.val) i) :
    0 < (placedLaw (Work.stageB h, phi)).mass u := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageB h, phi) u ht hle
  rw [placedLaw_mass_branch]
  exact_mod_cast stageBLaw_positive (aShape h.val) (bSplit ⟨h, b, false⟩)
    (bSplit_mem ⟨h, b, false⟩)

end MatrixMultiplication.AllFieldActiveGibbs

namespace MatrixMultiplication.AllFieldStageCGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws AllFieldActiveGibbs
open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def distinguishedSide {K : ℕ} (h : PartC K) (phi : Placement) : Fin 3 :=
  phi (stageCDistinguished (cShapeParent h))

def coordinateMass {K : ℕ} (h : PartC K) (k : Fin 17) : ℝ :=
  if k.val = 1 then
    (((1 - binaryParameter (cParameterParent h) (cShapeParent h)) / 2 : ℚ) : ℝ)
  else ((binaryParameter (cParameterParent h) (cShapeParent h) / 2 : ℚ) : ℝ)

def physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (side : Fin 3) (k : Fin 17) : ℝ :=
  if side = distinguishedSide h phi then Real.log (coordinateMass h k) else 0

theorem distinguishedSide_branch {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)).val =
      stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) := by
  simp only [distinguishedSide, branchShape, encodePhysicalShape_side,
    Equiv.symm_apply_apply, Work.splitShape, cSplit]

theorem placedLaw_stageC_branch_mass {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (placedLaw (Work.stageC h, phi)).mass (branchShape (Work.stageC h, phi) b) =
      coordinateMass h
        (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)) := by
  refine (placedLaw_mass_branch (Work.stageC h, phi) b).trans ?_
  change (stageCWeight (cParameterParent h) (cShapeParent h) b : ℝ) = _
  simp only [coordinateMass, distinguishedSide_branch]
  unfold stageCWeight
  have hm := stageCAtom_middle (cShapeParent h) (bShape_size h.1.val) h.1.property b
  by_cases hb : b.val < 2
  · have hn : ¬stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) = 1 :=
      fun hmiddle => (hm.mp hmiddle) hb
    simp only [hb, ite_true, hn, ite_false]
  · have hx := hm.mpr hb
    simp only [hb, ite_false, hx, ite_true]

theorem placedLaw_stageC_mass_of_positive {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageC h, phi) u hu
  exact placedLaw_stageC_branch_mass h phi b

theorem placedLaw_stageC_mass_on_feasible {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 2)
    (hle : ∀ s, (shapeSide s u).val ≤ physicalShape phi (cShapeParent h) s) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageC h, phi) u ht hle
  exact placedLaw_stageC_branch_mass h phi b

theorem sum_physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) :
    (∑ s : Fin 3, physicalPotential h phi s (shapeSide s u)) =
      Real.log (coordinateMass h (shapeSide (distinguishedSide h phi) u)) := by
  simp only [physicalPotential, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem placedLaw_stageC_log {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageC h, phi)).mass u) =
      physicalPotential h phi 0 (shapeSide 0 u) +
        physicalPotential h phi 1 (shapeSide 1 u) +
        physicalPotential h phi 2 (shapeSide 2 u) - 0 := by
  rw [placedLaw_stageC_mass_of_positive h phi u hu, ← sum_physicalPotential h phi u,
    Fin.sum_univ_three, sub_zero]

theorem placedLaw_positive_parent_bounds {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw w).mass u) :
    ∀ s, (shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch w u hu
  intro s
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

theorem jointCounts_positive_reference {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) : 0 < (placedLaw w).mass u := by
  have hc : (0 : ℝ) < (jointCounts allocation dilation w u : ℝ) := by exact_mod_cast hu
  rw [jointCounts_cast] at hc
  rcases mul_pos_iff.mp hc with hpos | hneg
  · exact hpos.2
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg _) hneg.1)

theorem localAllowed_positive_reference {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (counts : Hist → JointPopulation.Shape → ℕ) (total : Hist → ℕ)
    (hist : Hist) (word : Positions counts hist → JointPopulation.Shape)
    (hw : localAllowed counts total hist word)
    {K : ℕ} (h : PartC K) (phi : Placement) (htotal : total hist = 2)
    (hcounts : ∀ u, 0 < counts hist u → 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    ∀ i, 0 < (placedLaw (Work.stageC h, phi)).mass (word i) := by
  intro i
  have hbounds := JointMarginalSupport.localAllowed_parent_bounds counts total hist word hw
    (physicalShape phi (cShapeParent h))
    (fun u hu => placedLaw_positive_parent_bounds (Work.stageC h, phi) u (hcounts u hu))
  obtain ⟨j, hj⟩ := JointMarginalSupport.localAllowed_coordinate_witness
    counts total hist word hw (distinguishedSide h phi) i
  have hp : 0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) :=
    hcounts _ (symbol_count_pos counts (canonicalTarget counts) hist j)
  have ht : (word i).1.val + (word i).2.1.val + (word i).2.2.val = 2 :=
    (hw.1 i).trans htotal
  calc
    0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) := hp
    _ = coordinateMass h
        (shapeSide (distinguishedSide h phi) ((canonicalTarget counts hist).val j)) :=
      placedLaw_stageC_mass_of_positive h phi _ hp
    _ = coordinateMass h (shapeSide (distinguishedSide h phi) (word i)) := congrArg _ hj
    _ = (placedLaw (Work.stageC h, phi)).mass (word i) :=
      (placedLaw_stageC_mass_on_feasible h phi (word i) ht (hbounds i)).symm

end MatrixMultiplication.AllFieldStageCGibbs

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def potential {K : ℕ} (w : PlacedWork K) (s : Fin 3) (k : Fin 17) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.physicalPotential positiveInitial tableP
      (initialShape h.val) w.2 s k
  | .stageB h => AllFieldActiveGibbs.physicalPotential positiveSecond tablep
      (aShape h.val) w.2 s k
  | .stageC h => AllFieldStageCGibbs.physicalPotential h w.2 s k

def logNormalizer {K : ℕ} (w : PlacedWork K) : ℝ :=
  match w.1 with
  | .stageA h => AllFieldActiveGibbs.splitLogNormalizer positiveInitial tableP
      (initialShape h.val)
  | .stageB h => AllFieldActiveGibbs.splitLogNormalizer positiveSecond tablep
      (aShape h.val)
  | .stageC _ => 0

theorem placedLaw_log {K : ℕ} (w : PlacedWork K) (a : JointPopulation.Shape)
    (ha : 0 < (placedLaw w).mass a) :
    Real.log ((placedLaw w).mass a) = potential w 0 (shapeSide 0 a) +
      potential w 1 (shapeSide 1 a) + potential w 2 (shapeSide 2 a) -
        logNormalizer w := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact AllFieldActiveGibbs.placedLaw_stageA_log h phi a ha
  | stageB h => exact AllFieldActiveGibbs.placedLaw_stageB_log h phi a ha
  | stageC h => exact AllFieldStageCGibbs.placedLaw_stageC_log h phi a ha

theorem localAllowed_positive {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → JointPopulation.Shape → ℕ) (total : H → ℕ) (h : H)
    (word : Positions counts h → JointPopulation.Shape)
    (hw : localAllowed counts total h word) {K : ℕ} (w : PlacedWork K)
    (htotal : total h = 2 * w.1.halfLength)
    (hcounts : ∀ a, 0 < counts h a → 0 < (placedLaw w).mass a) :
    ∀ i, 0 < (placedLaw w).mass (word i) := by
  have hb := fun a ha =>
    AllFieldStageCGibbs.placedLaw_positive_parent_bounds w a (hcounts a ha)
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (initialShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageA_positive a phi u
        (hu.trans htotal) hle
  | stageB a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (aShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageB_positive a phi u
        (hu.trans htotal) hle
  | stageC a =>
      exact AllFieldStageCGibbs.localAllowed_positive_reference counts total h word hw
        a phi htotal hcounts

variable {K tick : ℕ} {sigma : Placement}

def orderTotal (h : ActiveOrder K tick sigma) : ℕ := 2 * h.val.val.1.halfLength

theorem canonicalLaw_mass_eq (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)) :
    (canonicalLaw (orderCounts allocation m) h).mass = (orderLaw h).mass := by
  have hcard : Fintype.card (Positions (orderCounts allocation m) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    simpa only [Positions, Fintype.card_fin] using orderCounts_sum allocation m h
  funext a
  rw [canonicalLaw_mass_of_pos _ h hpos, hcard]
  change (jointCounts allocation m h.val.val a : ℝ) /
    population allocation m (h.val.val.1.source, h.val.val.2) = _
  rw [jointCounts_cast]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (hcard ▸ hpos).ne')

theorem localAllowed_entropy_le (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (word : Positions (orderCounts allocation m) h → JointPopulation.Shape)
    (hw : localAllowed (orderCounts allocation m) orderTotal h word) :
    finiteEntropy (fun a => (wordPopulation word a : ℝ) /
      Fintype.card (Positions (orderCounts allocation m) h)) ≤
        finiteEntropy (orderLaw h).mass := by
  by_cases hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)
  · have hs := localAllowed_positive (orderCounts allocation m) orderTotal h word hw
      h.val.val rfl (fun a ha =>
        AllFieldStageCGibbs.jointCounts_positive_reference allocation m h.val.val a ha)
    have he := localAllowed_entropy_le_of_word_support (orderCounts allocation m)
      orderTotal h word (orderLaw h) (potential h.val.val 0) (potential h.val.val 1)
      (potential h.val.val 2) (logNormalizer h.val.val) hs
      (placedLaw_log h.val.val) hw
    have hc := canonicalLaw_mass_eq allocation m h hpos
    simpa only [gibbsCap, marginalError, FiniteLaw.map_mass, hc, sub_self, abs_zero,
      zero_mul, Finset.sum_const_zero, add_zero] using he
  · have hz := Nat.eq_zero_of_not_pos hpos
    simpa only [hz, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using (orderLaw h).entropy_nonneg

theorem tendsto_firstExponent (allocation : Allocation) (sigma : Placement) :
    Tendsto (fun m : ℕ => (∑ h : ActiveOrder K tick sigma,
      classExponent (orderCounts allocation m) (sigma 0)
        (triple (orderCounts allocation m) (canonicalTarget (orderCounts allocation m))) h
        (finiteEntropy (orderLaw h).mass)) / (m : ℝ)) atTop
      (𝓝 (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)) := by
  have hsize (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_total_div_of_coordinate_rates
      (fun m => orderCounts allocation m h)
      ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (orderLaw h).mass (orderLaw h).total (orderCounts_dilation_rate allocation h)
  have hside (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_weighted_target_side_entropy
      (fun m => orderCounts allocation m)
      (fun m => canonicalTarget (orderCounts allocation m))
      (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (fun h => (orderLaw h).mass) (fun h => (orderLaw h).total)
      (orderCounts_dilation_rate allocation) h (sigma 0)
  have hr := JointAmbientRateLimit.tendsto_sum_classExponent_div_nat
    (fun m => orderCounts allocation m) (sigma 0)
    (fun _ h => finiteEntropy (orderLaw h).mass)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)))
    hsize (fun h => (hsize h).mul_const (finiteEntropy (orderLaw h).mass))
    (fun h => by simpa only [Positions, Fintype.card_fin] using hside h)
  simpa only [orderNativeDegree, order_first_capacity, mul_sub] using hr

theorem eventually_sharedAmbient_first_card_le (allocation : Allocation)
    (sigma : Placement) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ e : Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m),
      ((sharedAmbient (orderCounts allocation m) orderTotal (sigma 0)
        (triple (orderCounts allocation m) e)).card : ℝ) ≤
      Real.exp ((m : ℝ) *
        (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)) := by
  filter_upwards [(tendsto_order.1
      (tendsto_firstExponent (K := K) (tick := tick) allocation sigma)).2
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)
      (lt_add_of_pos_right _ hε), eventually_gt_atTop (0 : ℕ)] with m hm hmp
  intro e
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmp
  have hb := sharedAmbient_card_le (orderCounts allocation m) orderTotal (sigma 0)
    (triple (orderCounts allocation m) e) (fun h => finiteEntropy (orderLaw h).mass)
    (fun h word hw => localAllowed_entropy_le allocation m h word hw)
  apply hb.trans
  simp_rw [classBound_eq_exp]
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  simp_rw [classExponent_target_eq]
  simpa only [mul_comm] using (div_le_iff₀ hmr).mp hm.le

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end MatrixAllFields

end OAI
