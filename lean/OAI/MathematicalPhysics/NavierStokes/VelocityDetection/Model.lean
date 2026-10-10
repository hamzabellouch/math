import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection
open scoped BigOperators Topology ContDiff
open Set Function Filter

abbrev Coord (n : ℕ) := Fin n → ℝ

abbrev ScalarField (n : ℕ) := ℝ → Coord n → ℝ

abbrev VectorField (n : ℕ) := ℝ → Coord n → Coord n

theorem neZeroTwo : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem neZeroFive : NeZero 5 := ⟨Nat.succ_ne_zero 4⟩

def spatialD {n : ℕ} (i : Fin n) (q : ScalarField n) : ScalarField n :=
  fun t x => deriv (fun s => q t (Function.update x i s)) (x i)

def timeD {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => derivWithin (fun s => q s x) (Ici 0) t

def laplacian {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (spatialD i q) t x

def advection {n : ℕ} (a : VectorField n) (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, a t x i * spatialD i q t x

def divergence {n : ℕ} (a : VectorField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (fun s y => a s y i) t x

def NavierStokes (ν : ℝ) (u : VectorField 3) (p : ScalarField 3)
    (f : VectorField 3) : Prop :=
  (∀ (t : ℝ), 0 ≤ t → ∀ x : Coord 3, ∀ i : Fin 3,
    timeD (fun s y => u s y i) t x + advection u (fun s y => u s y i) t x =
      -spatialD i p t x + ν * laplacian (fun s y => u s y i) t x + f t x i) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x, divergence u t x = 0) ∧
  (∀ x, u 0 x = 0)

def horizontal (x : Coord 3) : Coord 2 := ![x 0, x 1]

def liftScalar (q : ScalarField 2) : ScalarField 3 :=
  fun t x => q t (horizontal x)

def liftVelocity (a : VectorField 2) (w : ScalarField 2) : VectorField 3 :=
  fun t x => ![a t (horizontal x) 0, a t (horizontal x) 1, w t (horizontal x)]

@[simp] theorem horizontal_update_zero (x : Coord 3) (s : ℝ) :
    horizontal (Function.update x 0 s) = Function.update (horizontal x) 0 s := by
  ext i
  fin_cases i <;> simp [horizontal]

@[simp] theorem horizontal_update_one (x : Coord 3) (s : ℝ) :
    horizontal (Function.update x 1 s) = Function.update (horizontal x) 1 s := by
  ext i
  fin_cases i <;> simp [horizontal]

@[simp] theorem horizontal_update_two (x : Coord 3) (s : ℝ) :
    horizontal (Function.update x 2 s) = horizontal x := by
  ext i
  fin_cases i <;> simp [horizontal]

@[simp] theorem spatialD_lift_zero (q : ScalarField 2) :
    spatialD 0 (liftScalar q) = liftScalar (spatialD 0 q) := by
  funext t x
  simp only [spatialD, liftScalar, horizontal_update_zero]
  rfl

@[simp] theorem spatialD_lift_one (q : ScalarField 2) :
    spatialD 1 (liftScalar q) = liftScalar (spatialD 1 q) := by
  funext t x
  simp only [spatialD, liftScalar, horizontal_update_one]
  rfl

@[simp] theorem spatialD_lift_two (q : ScalarField 2) :
    spatialD 2 (liftScalar q) = 0 := by
  funext t x
  simp [spatialD, liftScalar]

@[simp] theorem spatialD_zero {n : ℕ} (i : Fin n) :
    spatialD i (0 : ScalarField n) = 0 := by
  funext t x
  simp [spatialD]

@[simp] theorem timeD_lift (q : ScalarField 2) :
    timeD (liftScalar q) = liftScalar (timeD q) := rfl

@[simp] theorem laplacian_lift (q : ScalarField 2) :
    laplacian (liftScalar q) = liftScalar (laplacian q) := by
  funext t x
  simp [laplacian, Fin.sum_univ_three, Fin.sum_univ_two, liftScalar]

@[simp] theorem advection_lift (a : VectorField 2) (w q : ScalarField 2) :
    advection (liftVelocity a w) (liftScalar q) = liftScalar (advection a q) := by
  funext t x
  simp [advection, Fin.sum_univ_three, Fin.sum_univ_two, liftVelocity, liftScalar]

@[simp] theorem divergence_lift (a : VectorField 2) (w : ScalarField 2) :
    divergence (liftVelocity a w) = liftScalar (divergence a) := by
  funext t x
  simp only [divergence, Fin.sum_univ_three, liftVelocity,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  change spatialD 0 (liftScalar (fun s y => a s y 0)) t x +
      spatialD 1 (liftScalar (fun s y => a s y 1)) t x +
      spatialD 2 (liftScalar w) t x = _
  simp [liftScalar, divergence, Fin.sum_univ_two]

def horizontalResidual (ν : ℝ) (a : VectorField 2) : VectorField 2 :=
  fun t x i => timeD (fun s y => a s y i) t x +
    advection a (fun s y => a s y i) t x -
    ν * laplacian (fun s y => a s y i) t x

def triangularForce (ν : ℝ) (a : VectorField 2) (h : ScalarField 2) : VectorField 3 :=
  liftVelocity (horizontalResidual ν a) h

theorem triangular_reduction (ν : ℝ) (a : VectorField 2) (w h : ScalarField 2)
    (ha : ∀ t, 0 ≤ t → ∀ x, divergence a t x = 0)
    (hw : ∀ t, 0 ≤ t → ∀ x,
      timeD w t x + advection a w t x = ν * laplacian w t x + h t x)
    (ha0 : ∀ x, a 0 x = 0) (hw0 : ∀ x, w 0 x = 0) :
    NavierStokes ν (liftVelocity a w) 0 (triangularForce ν a h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x i
    fin_cases i
    · change timeD (liftScalar (fun s y => a s y 0)) t x +
          advection (liftVelocity a w) (liftScalar (fun s y => a s y 0)) t x =
          -spatialD 0 0 t x + ν * laplacian (liftScalar (fun s y => a s y 0)) t x +
            horizontalResidual ν a t (horizontal x) 0
      simp only [timeD_lift, spatialD_zero, advection_lift, laplacian_lift]
      simp [liftScalar, horizontalResidual]
    · change timeD (liftScalar (fun s y => a s y 1)) t x +
          advection (liftVelocity a w) (liftScalar (fun s y => a s y 1)) t x =
          -spatialD 1 0 t x + ν * laplacian (liftScalar (fun s y => a s y 1)) t x +
            horizontalResidual ν a t (horizontal x) 1
      simp only [timeD_lift, spatialD_zero, advection_lift, laplacian_lift]
      simp [liftScalar, horizontalResidual]
    · change timeD (liftScalar w) t x +
          advection (liftVelocity a w) (liftScalar w) t x =
          -spatialD 2 0 t x + ν * laplacian (liftScalar w) t x + h t (horizontal x)
      simpa only [timeD_lift, advection_lift, laplacian_lift, spatialD_zero,
        Pi.zero_apply, neg_zero, zero_add, liftScalar] using hw t ht (horizontal x)
  · intro t ht x
    simpa only [divergence_lift, liftScalar] using ha t ht (horizontal x)
  · intro x
    ext i
    fin_cases i <;> simp [liftVelocity, ha0, hw0]

end VelocityDetection
end

end OAI
