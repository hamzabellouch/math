import OAI.Algebra.AuslanderReiten.Duality.LinearHomologyDuality
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Prod

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

abbrev Piece (n : ℕ) := Fin (n + 1) → k

omit [CommRing k] in
@[simp]
theorem cons_succ_castSucc {n : ℕ} (a : k) (f : Fin (n + 1) → k) (i : Fin n) :
    (Fin.cons a f : Fin (n + 2) → k) i.succ.castSucc = f i.castSucc := by
  rw [Fin.castSucc_succ]
  rfl

omit [CommRing k] in
@[simp]
theorem snoc_castSucc_succ {n : ℕ} (f : Fin (n + 1) → k) (a : k) (i : Fin n) :
    (Fin.snoc f a : Fin (n + 2) → k) i.castSucc.succ = f i.succ := by
  rw [← Fin.castSucc_succ, Fin.snoc_castSucc]

def mulX (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) where
  toFun f := Fin.cons 0 f
  map_add' f g := by ext i; cases i using Fin.cases <;> simp
  map_smul' a f := by ext i; cases i using Fin.cases <;> simp

def mulY (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) where
  toFun f := Fin.snoc f 0
  map_add' f g := by ext i; cases i using Fin.lastCases <;> simp
  map_smul' a f := by ext i; cases i using Fin.lastCases <;> simp

@[simp]
theorem mulX_zero (n : ℕ) (f : Piece k n) : mulX k n f 0 = 0 := rfl
@[simp]
theorem mulX_succ (n : ℕ) (f : Piece k n) (i : Fin (n + 1)) :
    mulX k n f i.succ = f i := rfl
@[simp]
theorem mulY_last (n : ℕ) (f : Piece k n) : mulY k n f (Fin.last (n + 1)) = 0 := by
  simp [mulY]
@[simp]
theorem mulY_castSucc (n : ℕ) (f : Piece k n) (i : Fin (n + 1)) :
    mulY k n f i.castSucc = f i := by simp [mulY]

theorem mulX_injective (n : ℕ) : Function.Injective (mulX k n) := by
  intro f g h
  ext i
  exact congrFun h i.succ

theorem mulY_injective (n : ℕ) : Function.Injective (mulY k n) := by
  intro f g h
  ext i
  have hi := congrFun h i.castSucc
  simpa using hi

theorem mul_commute (n : ℕ) : (mulX k (n + 1)).comp (mulY k n) =
    (mulY k (n + 1)).comp (mulX k n) := by
  apply LinearMap.ext
  intro f
  exact Fin.cons_snoc_eq_snoc_cons 0 f 0

def row (n : ℕ) : Piece k n × Piece k n →ₗ[k] Piece k (n + 1) :=
  (mulX k n).coprod (mulY k n)

def column (n : ℕ) : Piece k n →ₗ[k] Piece k (n + 1) × Piece k (n + 1) :=
  (mulY k n).prod (-(mulX k n))

@[simp]
theorem row_apply (n : ℕ) (u v : Piece k n) : row k n (u, v) = mulX k n u + mulY k n v := rfl

@[simp]
theorem column_apply (n : ℕ) (w : Piece k n) :
    column k n w = (mulY k n w, -(mulX k n w)) := rfl

theorem row_column (n : ℕ) : (row k (n + 1)).comp (column k n) = 0 := by
  apply LinearMap.ext
  intro w
  change mulX k (n + 1) (mulY k n w) + mulY k (n + 1) (-(mulX k n w)) = 0
  rw [map_neg, ← LinearMap.comp_apply, mul_commute]
  simp

theorem column_injective (n : ℕ) : Function.Injective (column k n) := by
  intro f g h
  apply mulY_injective k n
  exact congrArg Prod.fst h

theorem kernel_row (n : ℕ) (u v : Piece k (n + 1)) (h : row k (n + 1) (u, v) = 0) :
    ∃ w : Piece k n, column k n w = (u, v) := by
  let w : Piece k n := fun i => u i.castSucc
  have hu : u (Fin.last (n + 1)) = 0 := by
    have H := congrFun h (Fin.last (n + 2))
    simpa [row, mulX, mulY] using H
  have hv : v 0 = 0 := by
    have H := congrFun h 0
    simpa [row, mulX, mulY] using H
  have huv (i : Fin (n + 1)) : u i.castSucc + v i.succ = 0 := by
    have H := congrFun h i.castSucc.succ
    simpa [row, mulX, mulY] using H
  refine ⟨w, Prod.ext ?_ ?_⟩
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hu.symm
    · simp [w]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv.symm
    · change -w j = v j.succ
      exact (eq_neg_of_add_eq_zero_right (huv j)).symm

theorem range_column_eq_ker_row (n : ℕ) :
    LinearMap.range (column k n) = LinearMap.ker (row k (n + 1)) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (row_column k n)
  · rintro ⟨u, v⟩ h
    exact kernel_row k n u v h

theorem row_surjective (n : ℕ) : Function.Surjective (row k n) := by
  intro f
  let u : Piece k n := Pi.single (Fin.last n) (f (Fin.last (n + 1)))
  let v : Piece k n := fun i => f i.castSucc
  refine ⟨(u, v), ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [row, mulX, mulY, u]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [row, mulX, mulY, v]
    · simp [row, mulX, mulY, u, v]

theorem row_zero_injective : Function.Injective (row k 0) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : v 0 = v' 0 := by
    have H := congrFun h 0
    simpa [row, mulX, mulY] using H
  have hu : u 0 = u' 0 := by
    have H := congrFun h (Fin.last 1)
    change u 0 + 0 = u' 0 + 0 at H
    simpa using H
  apply Prod.ext
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    simpa [hi] using hu
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    simpa [hi] using hv

noncomputable def rowZeroEquiv : (Piece k 0 × Piece k 0) ≃ₗ[k] Piece k 1 :=
  LinearEquiv.ofBijective (row k 0) ⟨row_zero_injective k, row_surjective k 0⟩

end ArExplicit.BinaryKoszul

end OAI
