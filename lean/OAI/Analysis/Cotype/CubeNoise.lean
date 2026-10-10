import OAI.Analysis.Cotype.WalshDuality
import Mathlib.Tactic.Module

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubeCons (n : ℕ) : Bool × Cube n ≃ Cube (n+1) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, Fin.tail u)
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.cases (by simp) (fun i => by simp; rfl) i

theorem average_cons {n : ℕ} (f : Cube (n+1) → X) :
    average f = (1/2 : ℝ) • (average (fun u => f (Fin.cons false u)) +
      average (fun u => f (Fin.cons true u))) := by
  rw [← average_equiv (cubeCons n) f, average_prod]
  simp [average, cubeCons, smul_add, smul_smul, add_comm]

def cubeNoise : {n : ℕ} → (Cube n → X) → Cube n → X
  | 0, f, u => f u
  | _+1, f, u =>
    if u 0 then
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) (Fin.tail u) +
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) (Fin.tail u)
    else
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) (Fin.tail u) +
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) (Fin.tail u)

@[simp] theorem cubeNoise_cons_false {n : ℕ} (f : Cube (n+1) → X) (u : Cube n) :
    cubeNoise f (Fin.cons false u) =
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) u +
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) u := by simp [cubeNoise]

@[simp] theorem cubeNoise_cons_true {n : ℕ} (f : Cube (n+1) → X) (u : Cube n) :
    cubeNoise f (Fin.cons true u) =
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) u +
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) u := by simp [cubeNoise]

theorem cubeNoise_add {n : ℕ} (f g : Cube n → X) :
    cubeNoise (fun u => f u + g u) = fun u => cubeNoise f u + cubeNoise g u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem cubeNoise_smul {n : ℕ} (c : ℝ) (f : Cube n → X) :
    cubeNoise (fun u => c • f u) = fun u => c • cubeNoise f u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem cubeNoise_const {n : ℕ} (x : X) : cubeNoise (fun _ : Cube n => x) = fun _ => x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [cubeNoise, ih]
    split <;> module

theorem cubeNoise_norm_le {n : ℕ} (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [cubeNoise]
    split
    · exact (norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, smul_eq_mul]
        norm_num
        linarith [ih (fun v => f (Fin.cons false v)) (Fin.tail u),
          ih (fun v => f (Fin.cons true v)) (Fin.tail u)])
    · exact (norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, smul_eq_mul]
        norm_num
        linarith [ih (fun v => f (Fin.cons false v)) (Fin.tail u),
          ih (fun v => f (Fin.cons true v)) (Fin.tail u)])

theorem rademacherSum_cons {n : ℕ} (x : Fin (n+1) → X) (b : Bool) (u : Cube n) :
    rademacherSum X x (Fin.cons b u) = sign b • x 0 + rademacherSum X (fun i => x i.succ) u := by
  simp [rademacherSum, Fin.sum_univ_succ]

theorem cubeNoise_rademacherSum {n : ℕ} (x : Fin n → X) :
    cubeNoise (rademacherSum X x) = fun u => (1/2 : ℝ) • rademacherSum X x u := by
  induction n with
  | zero => funext u; simp [cubeNoise, rademacherSum]
  | succ n ih =>
    funext u
    obtain ⟨⟨b,v⟩, rfl⟩ := (cubeCons n).surjective u
    change cubeNoise (rademacherSum X x) (Fin.cons b v) =
      (1/2 : ℝ) • rademacherSum X x (Fin.cons b v)
    cases b <;> simp only [cubeNoise_cons_false, cubeNoise_cons_true, rademacherSum_cons,
      sign_false, sign_true, one_smul, neg_smul, cubeNoise_add, cubeNoise_const, ih]
    all_goals module

end Cotype

end

end OAI
