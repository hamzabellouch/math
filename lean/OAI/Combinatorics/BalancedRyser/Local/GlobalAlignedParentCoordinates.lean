import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct
import OAI.Combinatorics.BalancedRyser.Local.LocalParentMap
import OAI.Combinatorics.BalancedRyser.Local.OneReuseDecomposition

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition TupleAlignment AlignedUnused

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [DecidableEq F]

abbrev freeCoordinates {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (M : AlignedOffsets P a bits p) : FreeIndex P R → F :=
  (coordinates P R a bits p M).1

def underlyingFree {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b))
    (root child : Fin b) (r s : Fin 4) (bits : Bits b) (hne : root ≠ child)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s)
    (ij : Fin b × Fin 4) : FreeIndex P R :=
  ⟨ParentMap.underlying root child r s (bits root r) (bits child s) ij, by
    rw [hdep]
    exact ParentMap.underlying_not_dependent root child r s
      (bits root r) (bits child s) hne ij⟩

theorem free_point_eq_coordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (M : AlignedOffsets P a bits p) (ij : FreeIndex P R) :
    prescribedPoint P a bits M.1 ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm
        (freeCoordinates P a bits p R M ij)).1 := by
  exact (congrArg Subtype.val ((linePointEquiv (a.1 ij.1.1)
    (lineEval (a.1 ij.1.1) p)).symm_apply_apply
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩)).symm

theorem point_eq_of_underlying_coordinate_eq {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (R : Finset (Fin b)) (root child : Fin b) (r s : Fin 4)
    (hne : root ≠ child) (hshared : P.classOf root r = P.classOf child s)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s)
    (M N : AlignedOffsets P a bits p) (ij : Fin b × Fin 4)
    (h : freeCoordinates P a bits p R M (underlyingFree P R root child r s bits hne hdep ij) =
      freeCoordinates P a bits p R N (underlyingFree P R root child r s bits hne hdep ij)) :
    prescribedPoint P a bits M.1 ij = prescribedPoint P a bits N.1 ij := by
  let u := underlyingFree P R root child r s bits hne hdep ij
  have hbase : prescribedPoint P a bits M.1 u.1 = prescribedPoint P a bits N.1 u.1 := by
    rw [free_point_eq_coordinate P a bits p R M u,
      free_point_eq_coordinate P a bits p R N u, h]
  change prescribedPoint P a bits M.1
      (ParentMap.underlying root child r s (bits root r) (bits child s) ij) =
    prescribedPoint P a bits N.1
      (ParentMap.underlying root child r s (bits root r) (bits child s) ij) at hbase
  by_cases hf : ij = (child,s)
  · subst ij
    rw [ParentMap.underlying_first] at hbase
    have hm := ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
      root child r s hshared (bits child s)
    have hn := ParentMap.child_endpoint_eq_projection P a bits N.1 ha p N.2
      root child r s hshared (bits child s)
    simp only [ParentMap.endpointIndex, ite_true] at hm hn
    exact hm.trans ((congrArg (fun x => lineIntersection
      (lineThrough (a.2 (P.classOf root r)) x) (lineThrough (a.1 child) p)) hbase).trans hn.symm)
  · by_cases hs : ij = (child,s-1)
    · subst ij
      rw [ParentMap.underlying_second] at hbase
      have hm := ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
        root child r s hshared (!(bits child s))
      have hn := ParentMap.child_endpoint_eq_projection P a bits N.1 ha p N.2
        root child r s hshared (!(bits child s))
      have hbit : (!(bits child s)) ≠ bits child s := by cases bits child s <;> decide
      simp only [ParentMap.endpointIndex, ite_eq_right hbit] at hm hn
      exact hm.trans ((congrArg (fun x => lineIntersection
        (lineThrough (a.2 (P.classOf root r)) x) (lineThrough (a.1 child) p)) hbase).trans hn.symm)
    · simpa only [ParentMap.underlying, ite_eq_right hf, ite_eq_right hs] using hbase

theorem point_eq_of_free_coordinate_eq {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (M N : AlignedOffsets P a bits p)
    (ij : FreeIndex P R)
    (h : freeCoordinates P a bits p R M ij = freeCoordinates P a bits p R N ij) :
    prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a bits N.1 ij.1 := by
  rw [free_point_eq_coordinate P a bits p R M ij,
    free_point_eq_coordinate P a bits p R N ij, h]

def pointFromCoordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (root child : Fin b) (r s : Fin 4) (ij : Fin b × Fin 4) (x : F) : Point F :=
  let u := ParentMap.underlying root child r s (bits root r) (bits child s) ij
  let z := ((linePointEquiv (a.1 u.1) (lineEval (a.1 u.1) p)).symm x).1
  if ij ∈ ParentMap.dependent child s then
    lineIntersection (lineThrough (a.2 (P.classOf root r)) z)
      (lineThrough (a.1 ij.1) p)
  else z

omit [DecidableEq F] in
theorem point_eq_parent_projection {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (M : AlignedOffsets P a bits p)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M.1 ij =
      if ij ∈ ParentMap.dependent child s then
        lineIntersection (lineThrough (a.2 (P.classOf root r))
          (prescribedPoint P a bits M.1
            (ParentMap.underlying root child r s (bits root r) (bits child s) ij)))
          (lineThrough (a.1 ij.1) p)
      else prescribedPoint P a bits M.1
        (ParentMap.underlying root child r s (bits root r) (bits child s) ij) := by
  by_cases hd : ij ∈ ParentMap.dependent child s
  · rw [ite_eq_left hd]
    simp only [ParentMap.dependent, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · rw [ParentMap.underlying_first]
      simpa only [ParentMap.endpointIndex, ite_true] using
        ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
          root child r s hshared (bits child s)
    · rw [ParentMap.underlying_second]
      have hbit : (!(bits child s)) ≠ bits child s := by cases bits child s <;> decide
      simpa only [ParentMap.endpointIndex, ite_eq_right hbit] using
        ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
          root child r s hshared (!(bits child s))
  · rw [ite_eq_right hd, ParentMap.underlying_fixed root child r s
      (bits root r) (bits child s) hd]

theorem point_eq_pointFromCoordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (R : Finset (Fin b)) (root child : Fin b) (r s : Fin 4)
    (hne : root ≠ child) (hshared : P.classOf root r = P.classOf child s)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s)
    (M : AlignedOffsets P a bits p) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M.1 ij = pointFromCoordinate P a bits p root child r s ij
      (freeCoordinates P a bits p R M (underlyingFree P R root child r s bits hne hdep ij)) := by
  have hbase := free_point_eq_coordinate P a bits p R M
    (underlyingFree P R root child r s bits hne hdep ij)
  change prescribedPoint P a bits M.1
      (ParentMap.underlying root child r s (bits root r) (bits child s) ij) = _ at hbase
  exact (point_eq_parent_projection P a ha bits p M root child r s hshared ij).trans
    (congrArg (fun z => if ij ∈ ParentMap.dependent child s then
      lineIntersection (lineThrough (a.2 (P.classOf root r)) z)
        (lineThrough (a.1 ij.1) p) else z) hbase)

omit [DecidableEq F] in
theorem pointFromCoordinate_free {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (root child : Fin b) (r s : Fin 4) (ij : Fin b × Fin 4)
    (hij : ij ∉ ParentMap.dependent child s) :
    Function.Injective (pointFromCoordinate P a bits p root child r s ij) ∧
      ∀ x, OnLine (pointFromCoordinate P a bits p root child r s ij x)
        (lineThrough (a.1 ij.1) p) := by
  have heq (x : F) : pointFromCoordinate P a bits p root child r s ij x =
      ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).1 := by
    dsimp only [pointFromCoordinate]
    rw [ite_eq_right hij, ParentMap.underlying_fixed root child r s
      (bits root r) (bits child s) hij]
  constructor
  · intro x y h
    rw [heq, heq] at h
    exact (linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm.injective
      (Subtype.ext h)
  · intro x
    rw [heq]
    exact ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).2

structure PointSystem {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) where
  underlying : (Fin b × Fin 4) → FreeIndex P R
  point : (Fin b × Fin 4) → F → Point F
  free_fixed : ∀ v : FreeIndex P R, underlying v.1 = v
  free_injective : ∀ v : FreeIndex P R, Function.Injective (point v.1)
  free_onLine : ∀ (v : FreeIndex P R) x, OnLine (point v.1 x) (lineThrough (a.1 v.1.1) p)
  realizes : ∀ (M : AlignedOffsets P a bits p) ij,
    prescribedPoint P a bits M.1 ij = point ij ((coordinates P R a bits p M).1 (underlying ij))

def pointSystemOfNoDependents {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (hdep : dependentOccurrences P R = ∅) :
    PointSystem P a bits p R where
  underlying ij := ⟨ij, by rw [hdep]; simp⟩
  point ij x := ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).1
  free_fixed v := rfl
  free_injective v := by
    intro x y h
    exact (linePointEquiv (a.1 v.1.1) (lineEval (a.1 v.1.1) p)).symm.injective (Subtype.ext h)
  free_onLine v x := ((linePointEquiv (a.1 v.1.1) (lineEval (a.1 v.1.1) p)).symm x).2
  realizes M ij := free_point_eq_coordinate P a bits p R M ⟨ij, by rw [hdep]; simp⟩

def pointSystemOfLinkedPair {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (R : Finset (Fin b)) (root child : Fin b) (r s : Fin 4)
    (hne : root ≠ child) (hshared : P.classOf root r = P.classOf child s)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s) :
    PointSystem P a bits p R where
  underlying := underlyingFree P R root child r s bits hne hdep
  point := pointFromCoordinate P a bits p root child r s
  free_fixed v := by
    apply Subtype.ext
    exact ParentMap.underlying_fixed root child r s (bits root r) (bits child s)
      (by rw [← hdep]; exact v.2)
  free_injective v := (pointFromCoordinate_free P a bits p root child r s v.1
    (by rw [← hdep]; exact v.2)).1
  free_onLine v := (pointFromCoordinate_free P a bits p root child r s v.1
    (by rw [← hdep]; exact v.2)).2
  realizes M ij := point_eq_pointFromCoordinate P a ha bits p R root child r s
    hne hshared hdep M ij

theorem exists_smallReuse_pointSystem {b κ : ℕ} (P : EqualityPattern b κ)
    (hb : 3 ≤ b) (hκ : κ ≤ 1) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    ∃ R : Finset (Fin b), (dependentOccurrences P R).card = 2 * κ ∧
      Nonempty (PointSystem P a bits p R) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hκ with rfl | rfl
  · obtain ⟨R, _, _, hdep, _⟩ := exists_roots_with_exact_dependent_budget P hb (by omega)
    refine ⟨R, hdep, ⟨pointSystemOfNoDependents P a bits p R ?_⟩⟩
    exact Finset.card_eq_zero.mp (by simpa using hdep)
  · obtain ⟨R, root, child, r, s, _, _, _, hne, _, _, hshared, hdep, _⟩ :=
      exists_one_reuse_linked_pair P hb
    have hdep' : dependentOccurrences P R = ParentMap.dependent child s := hdep
    refine ⟨R, ?_, ⟨pointSystemOfLinkedPair P a ha bits p R root child r s hne hshared hdep'⟩⟩
    rw [hdep']
    have hne' : (child,s) ≠ (child,s-1) := by
      intro h
      exact ParentMap.sub_one_ne s (congrArg Prod.snd h).symm
    simp [ParentMap.dependent, hne']

end
end Balanced.Local.AlignedGlobal

end OAI
