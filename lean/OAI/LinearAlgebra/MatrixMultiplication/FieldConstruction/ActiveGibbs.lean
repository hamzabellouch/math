import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveLaws
import Mathlib.Data.Rat.BigOperators

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

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
  rw [splitWeight, Rat.cast_prod, Real.log_prod (s := Finset.univ) (fun i _ => hweight i)]
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
  change (Work.stageA h).Branch at b
  rw [placedLaw_mass_branch]
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
  change (Work.stageB h).Branch at b
  rw [placedLaw_mass_branch]
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

end

end OAI
