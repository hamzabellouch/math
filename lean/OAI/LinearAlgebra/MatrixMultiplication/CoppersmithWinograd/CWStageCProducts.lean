import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageC
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.TerminalProducts

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def SmallRow : Fin 4 → Type := ![Unit, Unit, Fin 5, Fin 5]

def SmallInner : Fin 4 → Type := ![Fin 5, Fin 5, Unit, Unit]

instance smallRowFintype (b : Fin 4) : Fintype (SmallRow b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallRow]; infer_instance

instance smallInnerFintype (b : Fin 4) : Fintype (SmallInner b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallInner]; infer_instance

instance smallRowDecidableEq (b : Fin 4) : DecidableEq (SmallRow b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallRow]; infer_instance

instance smallInnerDecidableEq (b : Fin 4) : DecidableEq (SmallInner b) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)))) b
  all_goals dsimp [SmallInner]; infer_instance

def Row (s : Fin 3) (b : Fin 4) : Type :=
  if s = 1 then SmallInner b else SmallRow b

def Middle (s : Fin 3) (b : Fin 4) : Type :=
  if s = 2 then SmallInner b else SmallRow b

def Column (s : Fin 3) (b : Fin 4) : Type :=
  if s = 0 then SmallInner b else SmallRow b

instance rowFintype (s : Fin 3) (b : Fin 4) : Fintype (Row s b) := by
  unfold Row; split_ifs <;> infer_instance
instance middleFintype (s : Fin 3) (b : Fin 4) : Fintype (Middle s b) := by
  unfold Middle; split_ifs <;> infer_instance
instance columnFintype (s : Fin 3) (b : Fin 4) : Fintype (Column s b) := by
  unfold Column; split_ifs <;> infer_instance
instance rowDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Row s b) := by
  unfold Row; split_ifs <;> infer_instance
instance middleDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Middle s b) := by
  unfold Middle; split_ifs <;> infer_instance
instance columnDecidableEq (s : Fin 3) (b : Fin 4) : DecidableEq (Column s b) := by
  unfold Column; split_ifs <;> infer_instance

abbrev Word := Fin 2 → Fin 7

def shape (s : Fin 3) : Fin 3 → ℕ := fun i => if i = s then 2 else 1

def source (F : Type*) [CommRing F] (s : Fin 3) : Tensor F Word Word Word :=
  CWStrands.shapeTensor (Fin 2) (shape s)

def canonicalAtom : Fin 4 → (Fin 3 → ℕ) :=
  ![![1, 1, 0], ![0, 0, 2], ![1, 0, 1], ![0, 1, 1]]

def branchAtom (s : Fin 3) (b : Fin 4) : Fin 3 → ℕ :=
  if s = 0 then ![canonicalAtom b 2, canonicalAtom b 1, canonicalAtom b 0]
  else if s = 1 then ![canonicalAtom b 0, canonicalAtom b 2, canonicalAtom b 1]
  else canonicalAtom b

def branchSource (F : Type*) [CommRing F] (s : Fin 3) (b : Fin 4) :
    Tensor F Word Word Word :=
  fun x y z =>
    if CWLeafStatistics.weight (x 0) = branchAtom s b 0 ∧
      CWLeafStatistics.weight (y 0) = branchAtom s b 1 ∧
      CWLeafStatistics.weight (z 0) = branchAtom s b 2
    then source F s x y z else 0

abbrev Positions (counts : Fin 4 → ℕ) := Σ b : Fin 4, Fin (counts b)

abbrev RowWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Row s p.1
abbrev MiddleWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Middle s p.1
abbrev ColumnWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Column s p.1

def singleCount (counts : Fin 4 → ℕ) : ℕ := counts 0 + counts 1
def crossCount (counts : Fin 4 → ℕ) : ℕ := counts 2 + counts 3
def totalCount (counts : Fin 4 → ℕ) : ℕ := singleCount counts + crossCount counts

variable (F : Type*) [CommRing F]

theorem coefficient_swapXZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 z y x := by
  simp only [FieldCW.tensor, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]
  ring

theorem coefficient_swapYZ (x y z : Fin 7) :
    FieldCW.tensor F 5 x y z = FieldCW.tensor F 5 x z y := by
  simp only [FieldCW.tensor, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]
  ring

theorem source_zero_apply (x y z : Word) :
    source F 0 x y z = source F 2 z y x := by
  have hs : CWStrands.strand (F := F) (Fin 2) x y z =
      CWStrands.strand (F := F) (Fin 2) z y x := by
    apply Finset.prod_congr rfl
    intro i hi
    exact coefficient_swapXZ F (x i) (y i) (z i)
  simp [source, CWStrands.shapeTensor, shape, hs, and_comm, and_assoc]

theorem source_one_apply (x y z : Word) :
    source F 1 x y z = source F 2 x z y := by
  have hs : CWStrands.strand (F := F) (Fin 2) x y z =
      CWStrands.strand (F := F) (Fin 2) x z y := by
    apply Finset.prod_congr rfl
    intro i hi
    exact coefficient_swapYZ F (x i) (y i) (z i)
  simp [source, CWStrands.shapeTensor, shape, hs, and_comm]

theorem source_two : source F 2 =
    CWStrands.shapeTensor (F := F) (Fin 2) ![1, 1, 2] := by
  congr 1

theorem canonical_pullback (b : Fin 4) :
    ∃ (a : (SmallRow b × SmallInner b) → Word)
      (c : (SmallInner b × SmallRow b) → Word)
      (e : (SmallRow b × SmallRow b) → Word),
      Tensor.pullback a c e (source F 2) =
        Tensor.matrixCoefficients (SmallRow b) (SmallInner b) (SmallRow b) := by
  rw [source_two]
  fin_cases b
  · exact ⟨_, _, _, CWStageC.branch1 F⟩
  · exact ⟨_, _, _, CWStageC.branch0 F⟩
  · exact ⟨_, _, _, CWStageC.branch3 F⟩
  · exact ⟨_, _, _, CWStageC.branch2 F⟩

theorem canonical_masked_pullback (b : Fin 4) :
    ∃ (a : (SmallRow b × SmallInner b) → Word)
      (c : (SmallInner b × SmallRow b) → Word)
      (e : (SmallRow b × SmallRow b) → Word),
      Tensor.pullback a c e (branchSource F 2 b) =
        Tensor.matrixCoefficients (SmallRow b) (SmallInner b) (SmallRow b) := by
  fin_cases b
  · refine ⟨(fun x : Unit × Fin 5 => ![CWStageC.interior x.2, 0]),
      (fun y : Fin 5 × Unit => ![CWStageC.interior y.1, 0]),
      (fun _ : Unit × Unit => ![0, 6]), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch1 F) x) y) z
    simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]
    exact h
  · refine ⟨(fun x : Unit × Fin 5 => ![0, CWStageC.interior x.2]),
      (fun y : Fin 5 × Unit => ![0, CWStageC.interior y.1]),
      (fun _ : Unit × Unit => ![6, 0]), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch0 F) x) y) z
    simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.last_weight, source_two]
    exact h
  · refine ⟨(fun x : Fin 5 × Unit => ![CWStageC.interior x.1, 0]),
      (fun y : Unit × Fin 5 => ![0, CWStageC.interior y.2]),
      (fun z : Fin 5 × Fin 5 => ![CWStageC.interior z.2, CWStageC.interior z.1]), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch3 F) x) y) z
    simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]
    exact h
  · refine ⟨(fun x : Fin 5 × Unit => ![0, CWStageC.interior x.1]),
      (fun y : Unit × Fin 5 => ![CWStageC.interior y.2, 0]),
      (fun z : Fin 5 × Fin 5 => ![CWStageC.interior z.1, CWStageC.interior z.2]), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch2 F) x) y) z
    simp [Tensor.pullback, branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]
    exact h

theorem branchSource_zero_apply (b : Fin 4) (x y z : Word) :
    branchSource F 0 b x y z = branchSource F 2 b z y x := by
  simp [branchSource, branchAtom, source_zero_apply,
    and_comm, and_assoc]

theorem branchSource_one_apply (b : Fin 4) (x y z : Word) :
    branchSource F 1 b x y z = branchSource F 2 b x z y := by
  simp [branchSource, branchAtom, source_one_apply,
    and_comm]

theorem oriented_pullback (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → Word)
      (c : (Middle s b × Column s b) → Word)
      (e : (Column s b × Row s b) → Word),
      Tensor.pullback a c e (source F s) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := canonical_pullback F b
  fin_cases s
  all_goals dsimp [Row, Middle, Column]
  · refine ⟨fun x => e x.swap, fun y => c y.swap, fun z => a z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h z.swap) y.swap) x.swap
    simpa [Tensor.pullback, source_zero_apply, Prod.swap,
      Tensor.matrixCoefficients, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · refine ⟨fun x => a x.swap, fun y => e y.swap, fun z => c z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h x.swap) z.swap) y.swap
    simpa [Tensor.pullback, source_one_apply, Prod.swap,
      Tensor.matrixCoefficients, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · exact ⟨a, c, e, h⟩

theorem oriented_masked_pullback (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → Word)
      (c : (Middle s b × Column s b) → Word)
      (e : (Column s b × Row s b) → Word),
      Tensor.pullback a c e (branchSource F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := canonical_masked_pullback F b
  fin_cases s
  all_goals dsimp [Row, Middle, Column]
  · refine ⟨fun x => e x.swap, fun y => c y.swap, fun z => a z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h z.swap) y.swap) x.swap
    simpa [Tensor.pullback, branchSource_zero_apply, Prod.swap,
      Tensor.matrixCoefficients, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · refine ⟨fun x => a x.swap, fun y => e y.swap, fun z => c z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h x.swap) z.swap) y.swap
    simpa [Tensor.pullback, branchSource_one_apply, Prod.swap,
      Tensor.matrixCoefficients, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · exact ⟨a, c, e, h⟩

theorem oriented_restriction (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → Word → F)
      (c : (Middle s b × Column s b) → Word → F)
      (e : (Column s b × Row s b) → Word → F),
      Tensor.restrict a c e (branchSource F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  classical
  obtain ⟨a, c, e, h⟩ := oriented_masked_pullback F s b
  refine ⟨(fun x w => if w = a x then 1 else 0),
    (fun y w => if w = c y then 1 else 0),
    (fun z w => if w = e z then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact h

def productSource (s : Fin 3) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → Word) (Positions counts → Word) (Positions counts → Word) :=
  CommonDimensions.familyProduct (fun p : Positions counts => branchSource F s p.1)

theorem product_restriction (s : Fin 3) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords s counts × MiddleWords s counts) → (Positions counts → Word) → F)
      (c : (MiddleWords s counts × ColumnWords s counts) → (Positions counts → Word) → F)
      (e : (ColumnWords s counts × RowWords s counts) → (Positions counts → Word) → F),
      Tensor.restrict a c e (productSource F s counts) =
        Tensor.matrixCoefficients (RowWords s counts) (MiddleWords s counts)
          (ColumnWords s counts) := by
  classical
  choose a c e h using fun p : Positions counts => oriented_restriction F s p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => branchSource F s p.1)
    (fun p => Row s p.1) (fun p => Middle s p.1) (fun p => Column s p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

end OAI
