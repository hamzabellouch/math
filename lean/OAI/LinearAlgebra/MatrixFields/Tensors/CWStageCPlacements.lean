import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.CommonDimensions
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryChildLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.TerminalProducts

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

theorem restrict_familyProduct {X Y Z X' Y' Z' : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h))
    (a : ∀ h, X' h → X h → K) (b : ∀ h, Y' h → Y h → K)
    (c : ∀ h, Z' h → Z h → K) :
    Tensor.restrict (fun x s => ∏ h, a h (x h) (s h))
      (fun y s => ∏ h, b h (y h) (s h)) (fun z s => ∏ h, c h (z h) (s h))
      (familyProduct T) = familyProduct (fun h => Tensor.restrict (a h) (b h) (c h) (T h)) := by
  funext x y z
  simp only [Tensor.restrict, familyProduct, Fintype.prod_sum, ← Finset.prod_mul_distrib]

theorem matrix_restriction_of_history_restrictions {X Y Z : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h)) (A B C : H → Type*)
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)]
    (a : ∀ h, (A h × B h) → X h → K) (b : ∀ h, (B h × C h) → Y h → K)
    (c : ∀ h, (C h × A h) → Z h → K)
    (hloc : ∀ h, Tensor.restrict (a h) (b h) (c h) (T h) =
      Tensor.matrixCoefficients (A h) (B h) (C h)) :
    ∃ (aa : ((∀ h, A h) × (∀ h, B h)) → (∀ h, X h) → K)
      (bb : ((∀ h, B h) × (∀ h, C h)) → (∀ h, Y h) → K)
      (cc : ((∀ h, C h) × (∀ h, A h)) → (∀ h, Z h) → K),
      Tensor.restrict aa bb cc (familyProduct T) =
        Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  have hp := restrict_familyProduct T a b c
  simp_rw [hloc] at hp
  obtain ⟨aa, bb, cc, hmatrix⟩ := matrix_familyProduct_restrict (K := K) A B C
  refine ⟨Tensor.composeRestrictionMatrix aa (fun x s => ∏ h, a h (x h) (s h)),
    Tensor.composeRestrictionMatrix bb (fun y s => ∏ h, b h (y h) (s h)),
    Tensor.composeRestrictionMatrix cc (fun z s => ∏ h, c h (z h) (s h)), ?_⟩
  rw [← Tensor.restrict_restrict, hp, hmatrix]

end MatrixMultiplication.TerminalProducts

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWStageC

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions

def interior (i : Fin 5) : Fin 7 := ⟨i.val + 1, by have := i.isLt; omega⟩

theorem interior_injective : Function.Injective interior := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa only [interior, Nat.add_right_cancel_iff] using hval

@[simp] theorem interior_weight (i : Fin 5) : CWLeafStatistics.weight (interior i) = 1 := by
  have hi : i.val + 1 ≠ 6 := by have := i.isLt; omega
  simp [CWLeafStatistics.weight, interior, hi]

@[simp] theorem zero_weight : CWLeafStatistics.weight (0 : Fin 7) = 0 := rfl

@[simp] theorem last_weight : CWLeafStatistics.weight (6 : Fin 7) = 2 := rfl

@[simp] theorem interior_complement (i : Fin 5) : complement 5 (interior i) = interior i := by
  apply complement_interior
  · simp [interior]
  · dsimp [interior]
    have := i.isLt
    omega

variable (F : Type*) [CommRing F]

theorem coefficient110 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) (interior j) 0 = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_last_zero_matching F 5 (interior i) (interior j)

theorem coefficient101 (i j : Fin 5) :
    FieldCW.tensor F 5 (interior i) 0 (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_middle_zero_matching F 5 (interior i) (interior j)

theorem coefficient011 (i j : Fin 5) :
    FieldCW.tensor F 5 0 (interior i) (interior j) = if i = j then 1 else 0 := by
  simpa only [interior_complement, interior_injective.eq_iff] using
    tensor_zero_matching F 5 (interior i) (interior j)

theorem coefficient002 : FieldCW.tensor F 5 0 0 6 = 1 := by
  simpa [complement, lastLabel] using tensor_zero_matching F 5 0 0

theorem branch0 :
    Tensor.pullback (fun x : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (interior x.2) Matrix.vecEmpty)))
      (fun y : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (interior y.1) Matrix.vecEmpty)))
      (fun _ : Unit × Unit => (Matrix.vecCons (6) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch1 :
    Tensor.pullback (fun x : Unit × Fin 5 => (Matrix.vecCons (interior x.2) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun y : Fin 5 × Unit => (Matrix.vecCons (interior y.1) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun _ : Unit × Unit => (Matrix.vecCons (0) (Matrix.vecCons (6) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit (Fin 5) Unit := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient002, coefficient110, Tensor.matrixCoefficients]

theorem branch2 :
    Tensor.pullback (fun x : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (interior x.1) Matrix.vecEmpty)))
      (fun y : Unit × Fin 5 => (Matrix.vecCons (interior y.2) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (interior z.1) (Matrix.vecCons (interior z.2) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

theorem branch3 :
    Tensor.pullback (fun x : Fin 5 × Unit => (Matrix.vecCons (interior x.1) (Matrix.vecCons (0) Matrix.vecEmpty)))
      (fun y : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (interior y.2) Matrix.vecEmpty)))
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (interior z.2) (Matrix.vecCons (interior z.1) Matrix.vecEmpty)))
      (shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients (Fin 5) Unit (Fin 5) := by
  funext x y z
  simp [Tensor.pullback, shapeTensor, weight, strand, Fin.sum_univ_succ,
    Fin.prod_univ_succ, interior_weight,
    coefficient011, coefficient101, Tensor.matrixCoefficients]
  all_goals (split_ifs <;> simp_all [eq_comm])

end MatrixMultiplication.CWStageC

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def SmallRow : Fin 4 → Type := (Matrix.vecCons (Unit) (Matrix.vecCons (Unit) (Matrix.vecCons (Fin 5) (Matrix.vecCons (Fin 5) Matrix.vecEmpty))))

def SmallInner : Fin 4 → Type := (Matrix.vecCons (Fin 5) (Matrix.vecCons (Fin 5) (Matrix.vecCons (Unit) (Matrix.vecCons (Unit) Matrix.vecEmpty))))

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
  (Matrix.vecCons ((Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (0) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (0) (Matrix.vecCons (2) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (1) (Matrix.vecCons (0) (Matrix.vecCons (1) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (1) (Matrix.vecCons (1) Matrix.vecEmpty)))) Matrix.vecEmpty))))

def branchAtom (s : Fin 3) (b : Fin 4) : Fin 3 → ℕ :=
  if s = 0 then (Matrix.vecCons (canonicalAtom b 2) (Matrix.vecCons (canonicalAtom b 1) (Matrix.vecCons (canonicalAtom b 0) Matrix.vecEmpty)))
  else if s = 1 then (Matrix.vecCons (canonicalAtom b 0) (Matrix.vecCons (canonicalAtom b 2) (Matrix.vecCons (canonicalAtom b 1) Matrix.vecEmpty)))
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
    CWStrands.shapeTensor (F := F) (Fin 2) (Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (2) Matrix.vecEmpty))) := by
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
  · refine ⟨(fun x : Unit × Fin 5 => (Matrix.vecCons (CWStageC.interior x.2) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun y : Fin 5 × Unit => (Matrix.vecCons (CWStageC.interior y.1) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun _ : Unit × Unit => (Matrix.vecCons (0) (Matrix.vecCons (6) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch1 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback,
      branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]
  · refine ⟨(fun x : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior x.2) Matrix.vecEmpty))),
      (fun y : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior y.1) Matrix.vecEmpty))),
      (fun _ : Unit × Unit => (Matrix.vecCons (6) (Matrix.vecCons (0) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch0 F) x) y) z
    convert h using 1 <;> rfl
  · refine ⟨(fun x : Fin 5 × Unit => (Matrix.vecCons (CWStageC.interior x.1) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun y : Unit × Fin 5 => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior y.2) Matrix.vecEmpty))),
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (CWStageC.interior z.2) (Matrix.vecCons (CWStageC.interior z.1) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch3 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback,
      branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]
  · refine ⟨(fun x : Fin 5 × Unit => (Matrix.vecCons (0) (Matrix.vecCons (CWStageC.interior x.1) Matrix.vecEmpty))),
      (fun y : Unit × Fin 5 => (Matrix.vecCons (CWStageC.interior y.2) (Matrix.vecCons (0) Matrix.vecEmpty))),
      (fun z : Fin 5 × Fin 5 => (Matrix.vecCons (CWStageC.interior z.1) (Matrix.vecCons (CWStageC.interior z.2) Matrix.vecEmpty))), ?_⟩
    funext x y z
    have h := congrFun (congrFun (congrFun (CWStageC.branch2 F) x) y) z
    convert h using 1 <;> first | rfl | simp [Tensor.pullback,
      branchSource, branchAtom, canonicalAtom,
      CWStageC.zero_weight, CWStageC.interior_weight, source_two]

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
  · refine ⟨fun x => e x.swap, fun y => c y.swap, fun z => a z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h z.swap) y.swap) x.swap
    simpa [Tensor.pullback, source_zero_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · refine ⟨fun x => a x.swap, fun y => e y.swap, fun z => c z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h x.swap) z.swap) y.swap
    simpa [Tensor.pullback, source_one_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · exact ⟨a, c, e, h⟩

theorem oriented_masked_pullback (s : Fin 3) (b : Fin 4) :
    ∃ (a : (Row s b × Middle s b) → Word)
      (c : (Middle s b × Column s b) → Word)
      (e : (Column s b × Row s b) → Word),
      Tensor.pullback a c e (branchSource F s b) =
        Tensor.matrixCoefficients (Row s b) (Middle s b) (Column s b) := by
  obtain ⟨a, c, e, h⟩ := canonical_masked_pullback F b
  fin_cases s
  · refine ⟨fun x => e x.swap, fun y => c y.swap, fun z => a z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h z.swap) y.swap) x.swap
    simpa [Tensor.pullback, branchSource_zero_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
  · refine ⟨fun x => a x.swap, fun y => e y.swap, fun z => c z.swap, ?_⟩
    funext x y z
    have hh := congrFun (congrFun (congrFun h x.swap) z.swap) y.swap
    simpa [Tensor.pullback, branchSource_one_apply, Row, Middle, Column,
      Tensor.matrixCoefficients, Prod.swap, eq_comm, and_comm, and_left_comm, and_assoc] using hh
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

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_positions (counts : Fin 4 → ℕ) :
    Fintype.card (Positions counts) = totalCount counts := by
  simp [Positions, Fintype.card_sigma, Fin.sum_univ_succ, totalCount,
    singleCount, crossCount, Nat.add_assoc]

theorem card_rowWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (RowWords s counts) =
      5 ^ (if s = 1 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Row, SmallRow, SmallInner, singleCount, crossCount, pow_add]

theorem card_middleWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (MiddleWords s counts) =
      5 ^ (if s = 2 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Middle, SmallRow, SmallInner, singleCount, crossCount, pow_add]

theorem card_columnWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (ColumnWords s counts) =
      5 ^ (if s = 0 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_pi, Fintype.prod_sigma]
  simp only [Fintype.card_eq_nat_card]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Column, SmallRow, SmallInner, singleCount, crossCount, pow_add]

def volume (s : Fin 3) (counts : Fin 4 → ℕ) : ℕ :=
  Fintype.card (RowWords s counts) * Fintype.card (MiddleWords s counts) *
    Fintype.card (ColumnWords s counts)

theorem volume_eq (s : Fin 3) (counts : Fin 4 → ℕ) :
    volume s counts = 5 ^ (singleCount counts + 2 * crossCount counts) := by
  rw [volume, card_rowWords, card_middleWords, card_columnWords]
  fin_cases s <;> simp [pow_add, two_mul] <;> ring

theorem volume_pos (s : Fin 3) (counts : Fin 4 → ℕ) : 0 < volume s counts := by
  rw [volume_eq]
  positivity

theorem log_volume (s : Fin 3) (counts : Fin 4 → ℕ) :
    Real.log (volume s counts : ℝ) =
      ((singleCount counts : ℝ) + 2 * crossCount counts) * Real.log 5 := by
  rw [volume_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_mul]

theorem normalized_log_volume (s : Fin 3) (counts : Fin 4 → ℕ)
    (hpos : 0 < totalCount counts) :
    Real.log (volume s counts : ℝ) / totalCount counts =
      (2 - (singleCount counts : ℝ) / totalCount counts) * Real.log 5 := by
  have hn : (totalCount counts : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have ht : (totalCount counts : ℝ) = singleCount counts + (crossCount counts : ℝ) := by
    simp [totalCount]
  rw [log_volume, mul_div_right_comm]
  congr 1
  field_simp [hn]
  rw [ht]
  ring

theorem totalCount_of_atom_counts (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    totalCount counts = n := by
  apply Nat.cast_injective (R := ℚ)
  calc
    (totalCount counts : ℚ) = ∑ i, (counts i : ℚ) := by
      simp [totalCount, singleCount, crossCount, Fin.sum_univ_succ, add_assoc]
    _ = n := by
      simp only [hc, ← Finset.mul_sum, AllFieldHistory.stageCWeight_normalized, mul_one]

theorem log_volume_of_atom_counts (s : Fin 3) (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    Real.log (volume s counts : ℝ) =
      (n : ℝ) * (2 - (AllFieldParameters.binaryParameter t u : ℝ)) * Real.log 5 := by
  have hs : (singleCount counts : ℚ) = (n : ℚ) * AllFieldParameters.binaryParameter t u := by
    simp only [singleCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_single]
  have hx : (crossCount counts : ℚ) =
      (n : ℚ) * (1 - AllFieldParameters.binaryParameter t u) := by
    simp only [crossCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_cross]
  have hsr : (singleCount counts : ℝ) =
      (n : ℝ) * (AllFieldParameters.binaryParameter t u : ℝ) := by exact_mod_cast hs
  have hxr : (crossCount counts : ℝ) =
      (n : ℝ) * (1 - (AllFieldParameters.binaryParameter t u : ℝ)) := by exact_mod_cast hx
  rw [log_volume, hsr, hxr]
  ring

theorem normalized_log_volume_of_atom_counts (s : Fin 3) (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ) (hn : 0 < n)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    Real.log (volume s counts : ℝ) / totalCount counts =
      (2 - (AllFieldParameters.binaryParameter t u : ℝ)) * Real.log 5 := by
  rw [log_volume_of_atom_counts s counts t u n hc, totalCount_of_atom_counts counts t u n hc]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hn']

variable {H : Type*} [Fintype H]

abbrev HistoryRowWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, RowWords (side h) (counts h)
abbrev HistoryMiddleWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, MiddleWords (side h) (counts h)
abbrev HistoryColumnWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, ColumnWords (side h) (counts h)

theorem card_historyRowWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryRowWords side counts) =
      5 ^ ∑ h, (if side h = 1 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_rowWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem card_historyMiddleWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryMiddleWords side counts) =
      5 ^ ∑ h, (if side h = 2 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_middleWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem card_historyColumnWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryColumnWords side counts) =
      5 ^ ∑ h, (if side h = 0 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_columnWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

def historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) : ℕ :=
  Fintype.card (HistoryRowWords side counts) *
    Fintype.card (HistoryMiddleWords side counts) *
      Fintype.card (HistoryColumnWords side counts)

theorem historyVolume_eq_prod (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts = ∏ h, volume (side h) (counts h) := by
  simp only [historyVolume, HistoryRowWords, HistoryMiddleWords, HistoryColumnWords,
    Fintype.card_pi, volume, Finset.prod_mul_distrib]

theorem historyVolume_eq (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts =
      5 ^ ∑ h, (singleCount (counts h) + 2 * crossCount (counts h)) := by
  rw [historyVolume_eq_prod]
  simp only [volume_eq]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem log_historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Real.log (historyVolume side counts : ℝ) =
      ∑ h, ((singleCount (counts h) : ℝ) + 2 * crossCount (counts h)) * Real.log 5 := by
  rw [historyVolume_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_sum,
    Nat.cast_add, Nat.cast_mul, Finset.sum_mul]

theorem log_historyVolume_of_mass_counts (side : H → Fin 3)
    (counts : H → Fin 4 → ℕ) (t u : H → AllFieldParameters.Shape)
    (mass : H → ℚ) (N : ℕ)
    (hc : ∀ h i, (counts h i : ℚ) =
      (N : ℚ) * mass h * AllFieldHistory.stageCWeight (t h) (u h) i) :
    Real.log (historyVolume side counts : ℝ) =
      (N : ℝ) * ∑ h, (mass h : ℝ) *
        (2 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) * Real.log 5 := by
  have hs (h : H) : (singleCount (counts h) : ℚ) =
      (N : ℚ) * mass h * AllFieldParameters.binaryParameter (t h) (u h) := by
    simp only [singleCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_single]
  have hx (h : H) : (crossCount (counts h) : ℚ) =
      (N : ℚ) * mass h * (1 - AllFieldParameters.binaryParameter (t h) (u h)) := by
    simp only [crossCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_cross]
  rw [log_historyVolume, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hsr : (singleCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (AllFieldParameters.binaryParameter (t h) (u h) : ℝ) := by
    exact_mod_cast hs h
  have hxr : (crossCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (1 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) := by
    exact_mod_cast hx h
  rw [hsr, hxr]
  ring

theorem normalized_log_historyVolume_of_mass_counts (side : H → Fin 3)
    (counts : H → Fin 4 → ℕ) (t u : H → AllFieldParameters.Shape)
    (mass : H → ℚ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ h i, (counts h i : ℚ) =
      (N : ℚ) * mass h * AllFieldHistory.stageCWeight (t h) (u h) i) :
    Real.log (historyVolume side counts : ℝ) / N =
      ∑ h, (mass h : ℝ) *
        (2 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) * Real.log 5 := by
  rw [log_historyVolume_of_mass_counts side counts t u mass N hc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  exact mul_div_cancel_left₀ _ hn

abbrev PopulationHistory (K : ℕ) := AllFieldHistory.PartC K × AllFieldHistory.Placement

def populationSide {K : ℕ} (h : PopulationHistory K) : Fin 3 :=
  h.2 (AllFieldHistory.stageCDistinguished (AllFieldHistory.cShapeParent h.1))

def populationAtomCounts {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) : ℕ :=
  AllFieldHistory.population allocation dilation (.afterC (h.1, i, false), h.2)

theorem populationAtomCounts_mass {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℚ) *
        AllFieldHistory.amount allocation (.partC h.1, h.2) *
          AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts, AllFieldHistory.population_cast]
  simp only [AllFieldHistory.amount, AllFieldHistory.canonicalAmount,
    AllFieldHistory.cAmount]
  ring

theorem populationAtomCounts_parent {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.population allocation dilation (.partC h.1, h.2) : ℚ) *
        AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
          (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts_mass, AllFieldHistory.population_cast]

theorem populationAtomCounts_total {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) :
    totalCount (populationAtomCounts allocation dilation h) =
      AllFieldHistory.population allocation dilation (.partC h.1, h.2) := by
  simpa [totalCount, singleCount, crossCount, populationAtomCounts,
    Fin.sum_univ_succ, Nat.add_assoc] using
    AllFieldHistory.c_population_transition allocation dilation h.1 false h.2

theorem log_population_historyVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (side : PopulationHistory K → Fin 3) :
    Real.log (historyVolume side (populationAtomCounts allocation dilation) : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 := by
  exact log_historyVolume_of_mass_counts side (populationAtomCounts allocation dilation)
    (fun h => AllFieldHistory.cParameterParent h.1)
    (fun h => AllFieldHistory.cShapeParent h.1)
    (fun h => AllFieldHistory.amount allocation (.partC h.1, h.2))
    (AllFieldHistory.populationLength (K := K) allocation dilation)
    (populationAtomCounts_mass allocation dilation)

theorem normalized_log_population_historyVolume {K : ℕ}
    (allocation : AllFieldHistory.Allocation) (dilation : ℕ) (hd : 0 < dilation)
    (side : PopulationHistory K → Fin 3) :
    Real.log (historyVolume side (populationAtomCounts allocation dilation) : ℝ) /
        AllFieldHistory.populationLength (K := K) allocation dilation =
      ∑ h : PopulationHistory K,
        (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
          (2 - (AllFieldParameters.binaryParameter
            (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 := by
  exact normalized_log_historyVolume_of_mass_counts side
    (populationAtomCounts allocation dilation)
    (fun h => AllFieldHistory.cParameterParent h.1)
    (fun h => AllFieldHistory.cShapeParent h.1)
    (fun h => AllFieldHistory.amount allocation (.partC h.1, h.2))
    (AllFieldHistory.populationLength (K := K) allocation dilation)
    (AllFieldPopulationCounts.blockLength_pos _ hd)
    (populationAtomCounts_mass allocation dilation)

def populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) : ℕ :=
  historyVolume (populationSide (K := K)) (populationAtomCounts allocation dilation)

theorem log_populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 :=
  log_population_historyVolume allocation dilation populationSide

theorem normalized_log_populationVolume {K : ℕ}
    (allocation : AllFieldHistory.Allocation) (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        AllFieldHistory.populationLength (K := K) allocation dilation =
      ∑ h : PopulationHistory K,
        (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
          (2 - (AllFieldParameters.binaryParameter
            (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 :=
  normalized_log_population_historyVolume allocation dilation hd populationSide

end MatrixMultiplication.CWStageCProducts

end

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def atomPermutation (s : Fin 3) (phi : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  if phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0 then Equiv.refl _
  else Equiv.swap 2 3

theorem branchAtom_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3))
    (b : Fin 4) (i : Fin 3) :
    branchAtom (phi s) (atomPermutation s phi b) (phi i) = branchAtom s b i := by
  revert s phi b i
  decide +kernel

theorem atomPermutation_single (s : Fin 3) (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    (atomPermutation s phi b).val < 2 ↔ b.val < 2 := by
  unfold atomPermutation
  split_ifs
  · rfl
  · fin_cases b <;> decide

theorem branchAtom_eq_stageCAtom (u : AllFieldParameters.Shape) (b : Fin 4) :
    branchAtom (AllFieldHistory.stageCDistinguished u) b = AllFieldHistory.stageCAtom u b := by
  rfl

theorem shape_eq_parent (u : AllFieldParameters.Shape)
    (hu : u ∈ AllFieldParameters.shapes 4) (hpos : AllFieldParameters.positive u = true) :
    shape (AllFieldHistory.stageCDistinguished u) = u := by
  rcases AllFieldHistory.positive_four_shapes u hu hpos with rfl | rfl | rfl <;>
    funext i <;> fin_cases i <;> rfl

theorem shape_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3)) (i : Fin 3) :
    shape (phi s) i = shape s (phi.symm i) := by
  have hiff : i = phi s ↔ phi.symm i = s := by
    constructor
    · intro h
      simp only [h, Equiv.symm_apply_apply]
    · intro h
      have hh := congrArg phi h
      simpa only [Equiv.apply_symm_apply] using hh
  simp only [shape, hiff]

def placedBranchSource (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) : Tensor F Word Word Word :=
  fun x y z =>
    if CWLeafStatistics.weight (x 0) = branchAtom s b (phi.symm 0) ∧
      CWLeafStatistics.weight (y 0) = branchAtom s b (phi.symm 1) ∧
      CWLeafStatistics.weight (z 0) = branchAtom s b (phi.symm 2)
    then source F (phi s) x y z else 0

theorem placedBranchSource_eq (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedBranchSource F s phi b = branchSource F (phi s) (atomPermutation s phi b) := by
  have h0 := branchAtom_transport s phi b (phi.symm 0)
  have h1 := branchAtom_transport s phi b (phi.symm 1)
  have h2 := branchAtom_transport s phi b (phi.symm 2)
  simp only [Equiv.apply_symm_apply] at h0 h1 h2
  funext x y z
  simp only [placedBranchSource, branchSource, h0, h1, h2]

theorem placed_branch_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → Word → F)
      (c : (Middle (phi s) b × Column (phi s) b) → Word → F)
      (e : (Column (phi s) b × Row (phi s) b) → Word → F),
      Tensor.restrict a c e (placedBranchSource F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  rw [placedBranchSource_eq]
  have h := oriented_restriction F (phi s) (atomPermutation s phi b)
  by_cases hp : phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0
  · have he : atomPermutation s phi = Equiv.refl _ := ite_eq_left hp
    rw [he] at h ⊢
    exact h
  · have he : atomPermutation s phi = Equiv.swap 2 3 := ite_eq_right hp
    rw [he] at h ⊢
    fin_cases b <;> norm_num only [Equiv.swap_apply_def] at h ⊢ <;> exact h

def placedProductSource (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → Word) (Positions counts → Word) (Positions counts → Word) :=
  CommonDimensions.familyProduct (fun p : Positions counts => placedBranchSource F s phi p.1)

theorem placed_product_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords (phi s) counts × MiddleWords (phi s) counts) →
        (Positions counts → Word) → F)
      (c : (MiddleWords (phi s) counts × ColumnWords (phi s) counts) →
        (Positions counts → Word) → F)
      (e : (ColumnWords (phi s) counts × RowWords (phi s) counts) →
        (Positions counts → Word) → F),
      Tensor.restrict a c e (placedProductSource F s phi counts) =
        Tensor.matrixCoefficients (RowWords (phi s) counts) (MiddleWords (phi s) counts)
          (ColumnWords (phi s) counts) := by
  classical
  choose a c e h using fun p : Positions counts => placed_branch_restriction F s phi p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => placedBranchSource F s phi p.1)
    (fun p => Row (phi s) p.1) (fun p => Middle (phi s) p.1)
    (fun p => Column (phi s) p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
