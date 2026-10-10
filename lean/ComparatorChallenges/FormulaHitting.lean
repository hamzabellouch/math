import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

namespace OAI

namespace NCHitting

abbrev Word (n : ℕ) := List (Fin n)
abbrev WordSeries (F : Type*) (n : ℕ) := Word n → F

def convolution {F : Type*} {n : ℕ} [Semiring F]
    (f g : WordSeries F n) : Word n → F
  | [] => f [] * g []
  | i :: w => f [] * g (i :: w) + convolution (fun v => f (i :: v)) g w

inductive Formula (F : Type*) (n : ℕ) where
  | scalar : F → Formula F n
  | var : Fin n → Formula F n
  | add : Formula F n → Formula F n → Formula F n
  | mul : Formula F n → Formula F n → Formula F n

namespace Formula

def size {F : Type*} {n : ℕ} : Formula F n → ℕ
  | scalar _ => 1
  | var _ => 1
  | add f g => f.size + g.size + 1
  | mul f g => f.size + g.size + 1

noncomputable def coeff {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → WordSeries F n
  | scalar a => fun w => if w = [] then a else 0
  | var i => fun w => if w = [i] then 1 else 0
  | add f g => fun w => coeff f w + coeff g w
  | mul f g => convolution (coeff f) (coeff g)

def eval {F A : Type*} {n : ℕ} [Semiring A]
    (scalarMap : F → A) (T : Fin n → A) : Formula F n → A
  | scalar a => scalarMap a
  | var i => T i
  | add f g => eval scalarMap T f + eval scalarMap T g
  | mul f g => eval scalarMap T f * eval scalarMap T g

end Formula

def dimension (n s : ℕ) : ℕ := if n = 1 ∧ s = 1 then 1 else 2 * n * s ^ 2

def matrixEntry (i r q : ℕ) : ℚ :=
  if q < r then (-1 : ℚ) ^ (r - q - 1) / ((r : ℚ) * (i : ℚ) ^ (r - q))
  else 0

def generator (n s : ℕ) : Fin n → Matrix (Fin (dimension n s)) (Fin (dimension n s)) ℚ :=
  fun i r q => if n = 1 ∧ s = 1 then 1 else matrixEntry (i.val + 1) r.val q.val

universe u_2

theorem universal_hitting (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (F : Type u_2) [Field F] [CharZero F] (f : Formula F n)
    (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  sorry

end NCHitting

end OAI
