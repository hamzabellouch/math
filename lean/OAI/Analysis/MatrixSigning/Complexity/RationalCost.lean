import Mathlib

namespace OAI

namespace KS.W08

open scoped BigOperators

structure RatCounted (α : Type*) where
  value : α
  ops : ℕ

namespace RatCounted

variable {α β : Type*}

def pure (x : α) : RatCounted α := ⟨x, 0⟩
def bind (x : RatCounted α) (f : α → RatCounted β) : RatCounted β :=
  let y := f x.value
  ⟨y.value, x.ops + y.ops⟩

def add (x y : ℚ) : RatCounted ℚ := ⟨x + y, 1⟩
def sub (x y : ℚ) : RatCounted ℚ := ⟨x - y, 1⟩
def mul (x y : ℚ) : RatCounted ℚ := ⟨x * y, 1⟩
def div (x y : ℚ) : RatCounted ℚ := ⟨x / y, 1⟩
def neg (x : ℚ) : RatCounted ℚ := ⟨-x, 1⟩
def inv (x : ℚ) : RatCounted ℚ := ⟨x⁻¹, 1⟩
def positive (x : ℚ) : RatCounted Bool := ⟨decide (0 < x), 1⟩

def traverse (n : ℕ) (f : Fin n → RatCounted α) : RatCounted (Vector α n) :=
  let computed := Vector.ofFn f
  ⟨computed.map (fun x => x.value), ∑ i, (computed.get i).ops⟩

@[simp] theorem traverse_value_get (n : ℕ) (f : Fin n → RatCounted α) (i : Fin n) :
    ((traverse n f).value).get i = (f i).value := by
  simp [traverse, Vector.get]
  rfl

@[simp] theorem traverse_ops (n : ℕ) (f : Fin n → RatCounted α) :
    (traverse n f).ops = ∑ i, (f i).ops := by
  simp [traverse, Vector.get]
  rfl

def sum : List ℚ → RatCounted ℚ
  | [] => pure 0
  | x :: xs => bind (sum xs) (fun s => add x s)

@[simp] theorem sum_value (xs : List ℚ) : (sum xs).value = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sum, bind, add, ih]

@[simp] theorem sum_ops (xs : List ℚ) : (sum xs).ops = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sum, bind, add, ih]

def dot (n : ℕ) (x y : Fin n → ℚ) : RatCounted ℚ :=
  bind (traverse n (fun i => mul (x i) (y i))) (fun p => sum p.toList)

@[simp] theorem dot_value (n : ℕ) (x y : Fin n → ℚ) :
    (dot n x y).value = ∑ i, x i * y i := by
  simp [dot, bind, traverse, mul, Vector.get]
  rw [← Vector.sum_toList, Vector.toList_ofFn, List.sum_ofFn]
  rfl

@[simp] theorem dot_ops (n : ℕ) (x y : Fin n → ℚ) :
    (dot n x y).ops = 2 * n := by
  simp [dot, bind, mul, two_mul]

end RatCounted

end KS.W08

end OAI
