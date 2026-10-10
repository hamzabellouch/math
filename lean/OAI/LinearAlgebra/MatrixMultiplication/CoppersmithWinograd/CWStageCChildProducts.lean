import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCPlacements

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

abbrev ChildPair := Fin 7 × Fin 7

def joinChildren (p : ChildPair) : Word := ![p.1, p.2]
def splitChildren (w : Word) : ChildPair := (w 0, w 1)

@[simp] theorem joinChildren_zero (p : ChildPair) : joinChildren p 0 = p.1 := rfl
@[simp] theorem joinChildren_one (p : ChildPair) : joinChildren p 1 = p.2 := rfl

@[simp] theorem join_split_children (w : Word) : joinChildren (splitChildren w) = w := by
  funext i
  fin_cases i <;> rfl

def siteTensor (F : Type*) [CommRing F] (g : Fin 3 → ℕ) :
    Tensor F (Fin 7) (Fin 7) (Fin 7) :=
  fun x y z => if CWLeafStatistics.weight x = g 0 ∧
    CWLeafStatistics.weight y = g 1 ∧ CWLeafStatistics.weight z = g 2
    then FieldCW.tensor F 5 x y z else 0

theorem siteTensor_support (F : Type*) [CommRing F] (g : Fin 3 → ℕ)
    (x y z : Fin 7) (h : siteTensor F g x y z ≠ 0) :
    CWLeafStatistics.weight x = g 0 ∧ CWLeafStatistics.weight y = g 1 ∧
      CWLeafStatistics.weight z = g 2 := by
  by_contra hn
  exact h (ite_eq_right hn)

theorem siteProduct_side_weights (F : Type*) [CommRing F] (g h : Fin 3 → ℕ)
    (x y z : ChildPair)
    (hne : Tensor.product (siteTensor F g) (siteTensor F h) x y z ≠ 0) (i : Fin 3) :
    CWLeafStatistics.weight ((![x, y, z] i).1) = g i ∧
      CWLeafStatistics.weight ((![x, y, z] i).2) = h i := by
  change siteTensor F g x.1 y.1 z.1 * siteTensor F h x.2 y.2 z.2 ≠ 0 at hne
  have hL : siteTensor F g x.1 y.1 z.1 ≠ 0 := by
    intro he
    exact hne (by simp [he])
  have hR : siteTensor F h x.2 y.2 z.2 ≠ 0 := by
    intro he
    exact hne (by simp [he])
  obtain ⟨hxL, hyL, hzL⟩ := siteTensor_support F g x.1 y.1 z.1 hL
  obtain ⟨hxR, hyR, hzR⟩ := siteTensor_support F h x.2 y.2 z.2 hR
  fin_cases i
  · exact ⟨hxL, hxR⟩
  · exact ⟨hyL, hyR⟩
  · exact ⟨hzL, hzR⟩

theorem siteTensor_eq_shapeTensor (F : Type*) [CommRing F] (g : Fin 3 → ℕ) :
    Tensor.pullback (fun (x : Fin 7) (_ : Fin 1) => x)
      (fun (y : Fin 7) (_ : Fin 1) => y) (fun (z : Fin 7) (_ : Fin 1) => z)
      (CWStrands.shapeTensor (F := F) (Fin 1) g) = siteTensor F g := by
  funext x y z
  simp [Tensor.pullback, CWStrands.shapeTensor, CWStrands.weight, CWStrands.strand,
    siteTensor]

def childProduct (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor F ChildPair ChildPair ChildPair :=
  Tensor.product (siteTensor F (branchAtom s b))
    (siteTensor F (fun i => shape s i - branchAtom s b i))

theorem branchAtom_le_shape (s : Fin 3) (b : Fin 4) (i : Fin 3) :
    branchAtom s b i ≤ shape s i := by
  fin_cases s <;> fin_cases b <;> fin_cases i <;> decide

theorem weight_joinChildren (x : ChildPair) :
    CWStrands.weight (joinChildren x) =
      CWLeafStatistics.weight x.1 + CWLeafStatistics.weight x.2 := by
  simp [CWStrands.weight, joinChildren, Fin.sum_univ_succ]

theorem strand_joinChildren (F : Type*) [CommRing F] (x y z : ChildPair) :
    CWStrands.strand (F := F) (Fin 2) (joinChildren x) (joinChildren y) (joinChildren z) =
      FieldCW.tensor F 5 x.1 y.1 z.1 * FieldCW.tensor F 5 x.2 y.2 z.2 := by
  simp [CWStrands.strand, joinChildren, Fin.prod_univ_succ]

theorem masked_eq_childProduct (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor.pullback joinChildren joinChildren joinChildren (branchSource F s b) =
      childProduct F s b := by
  funext x y z
  have h0 := branchAtom_le_shape s b 0
  have h1 := branchAtom_le_shape s b 1
  have h2 := branchAtom_le_shape s b 2
  by_cases hL : CWLeafStatistics.weight x.1 = branchAtom s b 0 ∧
      CWLeafStatistics.weight y.1 = branchAtom s b 1 ∧
      CWLeafStatistics.weight z.1 = branchAtom s b 2
  · have htotal :
        (CWLeafStatistics.weight x.1 + CWLeafStatistics.weight x.2 = shape s 0 ∧
          CWLeafStatistics.weight y.1 + CWLeafStatistics.weight y.2 = shape s 1 ∧
          CWLeafStatistics.weight z.1 + CWLeafStatistics.weight z.2 = shape s 2) ↔
        (CWLeafStatistics.weight x.2 = shape s 0 - branchAtom s b 0 ∧
          CWLeafStatistics.weight y.2 = shape s 1 - branchAtom s b 1 ∧
          CWLeafStatistics.weight z.2 = shape s 2 - branchAtom s b 2) := by
      rcases hL with ⟨hx, hy, hz⟩
      constructor <;> rintro ⟨ha, hb, hc⟩ <;>
        exact ⟨by omega, by omega, by omega⟩
    simp only [hL.1, hL.2.1, hL.2.2] at htotal
    simp [Tensor.pullback, branchSource, source, CWStrands.shapeTensor,
      weight_joinChildren, strand_joinChildren, childProduct, Tensor.product, siteTensor,
      hL, htotal, mul_ite]
  · simp [Tensor.pullback, branchSource, childProduct, Tensor.product, siteTensor, hL]

theorem childProduct_split (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4)
    (x y z : Word) :
    childProduct F s b (splitChildren x) (splitChildren y) (splitChildren z) =
      branchSource F s b x y z := by
  have h := congrFun (congrFun (congrFun (masked_eq_childProduct F s b)
    (splitChildren x)) (splitChildren y)) (splitChildren z)
  simpa only [Tensor.pullback, join_split_children] using h.symm

theorem childProduct_pullback (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → ChildPair)
      (c : (Middle s b × Column s b) → ChildPair)
      (e : (Column s b × Row s b) → ChildPair),
      Tensor.pullback a c e (childProduct F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := oriented_masked_pullback F s b
  refine ⟨splitChildren ∘ a, splitChildren ∘ c, splitChildren ∘ e, ?_⟩
  funext x y z
  change childProduct F s b (splitChildren (a x)) (splitChildren (c y))
    (splitChildren (e z)) = _
  rw [childProduct_split]
  exact congrFun (congrFun (congrFun h x) y) z

theorem childProduct_restriction (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → ChildPair → F)
      (c : (Middle s b × Column s b) → ChildPair → F)
      (e : (Column s b × Row s b) → ChildPair → F),
      Tensor.restrict a c e (childProduct F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  classical
  obtain ⟨a, c, e, h⟩ := childProduct_pullback F s b
  refine ⟨(fun x w => if w = a x then 1 else 0),
    (fun y w => if w = c y then 1 else 0),
    (fun z w => if w = e z then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact h

def placedChildProduct (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :=
  childProduct F (phi s) (atomPermutation s phi b)

theorem placedChildProduct_eq (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedChildProduct F s phi b =
      Tensor.product (siteTensor F (fun i => branchAtom s b (phi.symm i)))
        (siteTensor F (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i))) := by
  have ha : branchAtom (phi s) (atomPermutation s phi b) =
      fun i => branchAtom s b (phi.symm i) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using branchAtom_transport s phi b (phi.symm i)
  have hs : shape (phi s) = fun i => shape s (phi.symm i) := by
    funext i
    exact shape_transport s phi i
  simp only [placedChildProduct, childProduct, ha, hs]

theorem placedChildProduct_eq_stageC (F : Type*) [CommRing F]
    (u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedChildProduct F (AllFieldHistory.stageCDistinguished u) phi b =
      Tensor.product (siteTensor F (fun i => AllFieldHistory.stageCAtom u b (phi.symm i)))
        (siteTensor F (fun i => u (phi.symm i) -
          AllFieldHistory.stageCAtom u b (phi.symm i))) := by
  rw [placedChildProduct_eq, branchAtom_eq_stageCAtom, shape_eq_parent u hu hpos]

theorem placedChildProduct_side_weights (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) (x y z : ChildPair)
    (hne : placedChildProduct F s phi b x y z ≠ 0) (i : Fin 3) :
    CWLeafStatistics.weight ((![x, y, z] i).1) = branchAtom s b (phi.symm i) ∧
      CWLeafStatistics.weight ((![x, y, z] i).2) =
        shape s (phi.symm i) - branchAtom s b (phi.symm i) := by
  rw [placedChildProduct_eq] at hne
  exact siteProduct_side_weights F _ _ x y z hne i

theorem placedChildProduct_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → ChildPair → F)
      (c : (Middle (phi s) b × Column (phi s) b) → ChildPair → F)
      (e : (Column (phi s) b × Row (phi s) b) → ChildPair → F),
      Tensor.restrict a c e (placedChildProduct F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  have h := childProduct_restriction F (phi s) (atomPermutation s phi b)
  unfold placedChildProduct
  by_cases hp : phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0
  · have he : atomPermutation s phi = Equiv.refl _ := ite_eq_left hp
    rw [he] at h ⊢
    exact h
  · have he : atomPermutation s phi = Equiv.swap 2 3 := ite_eq_right hp
    rw [he] at h ⊢
    fin_cases b <;> exact h

def placedChildProducts (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → ChildPair) (Positions counts → ChildPair)
      (Positions counts → ChildPair) :=
  CommonDimensions.familyProduct (fun p : Positions counts => placedChildProduct F s phi p.1)

theorem placedChildProducts_side_weights (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ)
    (x y z : Positions counts → ChildPair)
    (hne : placedChildProducts F s phi counts x y z ≠ 0)
    (p : Positions counts) (i : Fin 3) :
    CWLeafStatistics.weight ((![x p, y p, z p] i).1) = branchAtom s p.1 (phi.symm i) ∧
      CWLeafStatistics.weight ((![x p, y p, z p] i).2) =
        shape s (phi.symm i) - branchAtom s p.1 (phi.symm i) := by
  have hp : placedChildProduct F s phi p.1 (x p) (y p) (z p) ≠ 0 := by
    intro he
    exact hne (Finset.prod_eq_zero (Finset.mem_univ p) he)
  exact placedChildProduct_side_weights F s phi p.1 (x p) (y p) (z p) hp i

theorem placedChildProducts_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords (phi s) counts × MiddleWords (phi s) counts) →
        (Positions counts → ChildPair) → F)
      (c : (MiddleWords (phi s) counts × ColumnWords (phi s) counts) →
        (Positions counts → ChildPair) → F)
      (e : (ColumnWords (phi s) counts × RowWords (phi s) counts) →
        (Positions counts → ChildPair) → F),
      Tensor.restrict a c e (placedChildProducts F s phi counts) =
        Tensor.matrixCoefficients (RowWords (phi s) counts) (MiddleWords (phi s) counts)
          (ColumnWords (phi s) counts) := by
  classical
  choose a c e h using fun p : Positions counts => placedChildProduct_restriction F s phi p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => placedChildProduct F s phi p.1)
    (fun p => Row (phi s) p.1) (fun p => Middle (phi s) p.1)
    (fun p => Column (phi s) p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

end OAI
