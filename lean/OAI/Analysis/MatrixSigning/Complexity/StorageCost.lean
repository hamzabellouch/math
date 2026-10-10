import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseRatMatrix
import OAI.Analysis.MatrixSigning.Complexity.RationalCost

namespace OAI

namespace KS.W08

open KS.W07
open scoped BigOperators

structure AccessCounted (α : Type*) where
  value : α
  reads : ℕ
  writes : ℕ
  copies : ℕ
  ops : ℕ := 0

namespace AccessCounted

variable {α β : Type*}

def pure (x : α) : AccessCounted α := ⟨x, 0, 0, 0, 0⟩

def bind (x : AccessCounted α) (f : α → AccessCounted β) : AccessCounted β :=
  let y := f x.value
  ⟨y.value, x.reads + y.reads, x.writes + y.writes, x.copies + y.copies, x.ops + y.ops⟩

def work (x : AccessCounted α) : ℕ := x.reads + x.writes + x.copies

def add (x y : ℚ) : AccessCounted ℚ := ⟨x + y, 0, 0, 0, 1⟩
def sub (x y : ℚ) : AccessCounted ℚ := ⟨x - y, 0, 0, 0, 1⟩
def mul (x y : ℚ) : AccessCounted ℚ := ⟨x * y, 0, 0, 0, 1⟩
def div (x y : ℚ) : AccessCounted ℚ := ⟨x / y, 0, 0, 0, 1⟩
def neg (x : ℚ) : AccessCounted ℚ := ⟨-x, 0, 0, 0, 1⟩
def inv (x : ℚ) : AccessCounted ℚ := ⟨x⁻¹, 0, 0, 0, 1⟩
def positive (x : ℚ) : AccessCounted Bool := ⟨decide (0 < x), 0, 0, 0, 1⟩

@[simp] theorem add_work (x y : ℚ) : (add x y).work = 0 := rfl
@[simp] theorem sub_work (x y : ℚ) : (sub x y).work = 0 := rfl
@[simp] theorem mul_work (x y : ℚ) : (mul x y).work = 0 := rfl
@[simp] theorem div_work (x y : ℚ) : (div x y).work = 0 := rfl
@[simp] theorem neg_work (x : ℚ) : (neg x).work = 0 := rfl
@[simp] theorem inv_work (x : ℚ) : (inv x).work = 0 := rfl
@[simp] theorem positive_work (x : ℚ) : (positive x).work = 0 := rfl

def erase (x : AccessCounted α) : RatCounted α := ⟨x.value, x.ops⟩

abbrev toArithmetic (x : AccessCounted α) : RatCounted α := erase x

def ofArithmetic (x : RatCounted α) : AccessCounted α := ⟨x.value, 0, 0, 0, x.ops⟩

@[simp] theorem ofArithmetic_value (x : RatCounted α) : (ofArithmetic x).value = x.value := rfl
@[simp] theorem ofArithmetic_ops (x : RatCounted α) : (ofArithmetic x).ops = x.ops := rfl
@[simp] theorem ofArithmetic_work (x : RatCounted α) : (ofArithmetic x).work = 0 := rfl
@[simp] theorem erase_ofArithmetic (x : RatCounted α) : (ofArithmetic x).erase = x := by
  cases x
  rfl
@[simp] theorem erase_pure (x : α) : (pure x).erase = RatCounted.pure x := rfl
@[simp] theorem erase_bind (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).erase = RatCounted.bind x.erase (fun v => (f v).erase) := rfl

theorem erase_eq_of_value_ops (x : AccessCounted α) (y : RatCounted α)
    (hv : x.value = y.value) (ho : x.ops = y.ops) : x.erase = y := by
  cases x
  cases y
  simp_all [erase]

@[simp] theorem pure_ops (x : α) : (pure x).ops = 0 := rfl
@[simp] theorem bind_ops (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).ops = x.ops + (f x.value).ops := rfl

@[simp] theorem pure_work (x : α) : (pure x).work = 0 := rfl

@[simp] theorem bind_work (x : AccessCounted α) (f : α → AccessCounted β) :
    (bind x f).work = x.work + (f x.value).work := by simp [bind, work]; omega

theorem bind_work_le (x : AccessCounted α) (f : α → AccessCounted β) (a b : ℕ)
    (hx : x.work ≤ a) (hf : ∀ v, (f v).work ≤ b) : (bind x f).work ≤ a + b := by
  rw [bind_work]
  exact Nat.add_le_add hx (hf x.value)

def readVector {n : ℕ} (v : Vector ℚ n) (i : Fin n) : AccessCounted ℚ :=
  let saved := Vector.ofFn v.get
  ⟨saved.get i, n + 1, n, 1, 0⟩

@[simp] theorem readVector_value {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).value = v.get i := by
  simp [readVector, Vector.get]
  rfl

@[simp] theorem readVector_ops {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).ops = 0 := rfl

@[simp] theorem readVector_work {n : ℕ} (v : Vector ℚ n) (i : Fin n) :
    (readVector v i).work = 2 * n + 2 := by simp [readVector, work]; omega

def readMatrix {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) : AccessCounted ℚ :=
  let saved := DenseRatMatrix.ofMatrix (DenseRatMatrix.decode M)
  ⟨DenseRatMatrix.decode saved i j, 2 * n * n + 2, n * n + n, 1, 0⟩

@[simp] theorem readMatrix_value {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).value = DenseRatMatrix.decode M i j := by simp [readMatrix]

@[simp] theorem readMatrix_ops {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).ops = 0 := rfl

@[simp] theorem readMatrix_work {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (readMatrix M i j).work = 3 * n ^ 2 + n + 3 := by simp [readMatrix, work]; ring

def traverse (n : ℕ) (f : Fin n → AccessCounted α) : AccessCounted (Vector α n) :=
  let computed := Vector.ofFn f
  ⟨computed.map (fun x => x.value), ∑ i, (computed.get i).reads,
    n + ∑ i, (computed.get i).writes, ∑ i, (computed.get i).copies,
    ∑ i, (computed.get i).ops⟩

@[simp] theorem traverse_value_get (n : ℕ) (f : Fin n → AccessCounted α) (i : Fin n) :
    (traverse n f).value.get i = (f i).value := by
  simp [traverse, Vector.get]
  rfl

@[simp] theorem traverse_ops (n : ℕ) (f : Fin n → AccessCounted α) :
    (traverse n f).ops = ∑ i, (f i).ops := by
  simp [traverse, Vector.get]
  rfl

@[simp] theorem erase_traverse (n : ℕ) (f : Fin n → AccessCounted α) :
    (traverse n f).erase = RatCounted.traverse n (fun i => (f i).erase) := by
  apply erase_eq_of_value_ops
  · apply Vector.ext
    intro i hi
    simp [traverse, RatCounted.traverse, erase, Vector.get]
  · simp [erase]

@[simp] theorem traverse_work (n : ℕ) (f : Fin n → AccessCounted α) :
    (traverse n f).work = n + ∑ i, (f i).work := by
  simp [traverse, work, Vector.get, Finset.sum_add_distrib]
  change (∑ i, (f i).reads) + (n + ∑ i, (f i).writes) + (∑ i, (f i).copies) =
    n + ((∑ i, (f i).reads) + (∑ i, (f i).writes) + (∑ i, (f i).copies))
  omega

theorem traverse_work_le (n : ℕ) (f : Fin n → AccessCounted α) (b : ℕ)
    (h : ∀ i, (f i).work ≤ b) : (traverse n f).work ≤ n * (b + 1) := by
  rw [traverse_work]
  calc
    _ ≤ n + ∑ _i : Fin n, b := Nat.add_le_add_left
      (Finset.sum_le_sum (fun i _ => h i)) n
    _ = _ := by simp; ring

def sumVector {n : ℕ} (v : Vector ℚ n) : AccessCounted ℚ :=
  ⟨(RatCounted.sum v.toList).value, 2 * n, n, 0, n⟩

@[simp] theorem sumVector_value {n : ℕ} (v : Vector ℚ n) :
    (sumVector v).value = v.toList.sum := by simp [sumVector]

@[simp] theorem sumVector_ops {n : ℕ} (v : Vector ℚ n) :
    (sumVector v).ops = n := rfl

@[simp] theorem sumVector_work {n : ℕ} (v : Vector ℚ n) :
    (sumVector v).work = 3 * n := by simp [sumVector, work]; omega

def dot (n : ℕ) (x y : Fin n → AccessCounted ℚ) : AccessCounted ℚ :=
  bind (traverse n (fun i => bind (x i) (fun a => bind (y i) (fun b => mul a b))))
    sumVector

@[simp] theorem dot_value (n : ℕ) (x y : Fin n → AccessCounted ℚ) :
    (dot n x y).value = ∑ i, (x i).value * (y i).value := by
  simp [dot, bind, mul, traverse, Vector.get]
  rw [← Vector.sum_toList, Vector.toList_ofFn, List.sum_ofFn]
  rfl

@[simp] theorem dot_work (n : ℕ) (x y : Fin n → AccessCounted ℚ) :
    (dot n x y).work = 4 * n + ∑ i, ((x i).work + (y i).work) := by
  simp [dot, traverse_work, bind_work]
  omega

@[simp] theorem dot_ops (n : ℕ) (x y : Fin n → AccessCounted ℚ) :
    (dot n x y).ops = 2 * n + ∑ i, ((x i).ops + (y i).ops) := by
  simp [dot, bind_ops, traverse_ops, mul, Finset.sum_add_distrib]
  ring

theorem dot_work_le (n : ℕ) (x y : Fin n → AccessCounted ℚ) (a b : ℕ)
    (hx : ∀ i, (x i).work ≤ a) (hy : ∀ i, (y i).work ≤ b) :
    (dot n x y).work ≤ n * (a + b + 4) := by
  rw [dot_work]
  calc
    _ ≤ 4 * n + ∑ _i : Fin n, (a + b) := Nat.add_le_add_left
      (Finset.sum_le_sum (fun i _ => Nat.add_le_add (hx i) (hy i))) _
    _ = _ := by simp; ring

end AccessCounted
end KS.W08

end OAI
