import OAI.Analysis.Cotype.WalshNorm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubeJoin (n j : ℕ) : Cube n × Cube j ≃ Cube (n+j) where
  toFun p := Fin.append p.1 p.2
  invFun u := (fun i => u (Fin.castAdd j i), fun i => u (Fin.natAdd n i))
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.addCases (by simp) (by simp) i

@[simp] theorem cubeJoin_apply {n j : ℕ} (a : Cube n) (b : Cube j) :
    cubeJoin n j (a,b) = Fin.append a b := rfl

theorem character_join {n j : ℕ} (a c : Cube n) (b d : Cube j) :
    character (cubeJoin n j (a,b)) (cubeJoin n j (c,d)) =
      character a c * character b d := by
  simp [character, Fin.prod_univ_add]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → X) : average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
  simp [mul_comm]

theorem average_join {n j : ℕ} (f : Cube (n+j) → X) :
    average f = average (fun a => average (fun b => f (cubeJoin n j (a,b)))) := by
  rw [← average_equiv (cubeJoin n j) f, average_prod]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

omit [NormedSpace ℝ X] in
theorem cubeL2_join {n j : ℕ} (f : Cube (n+j) → X) :
    cubeL2 X f = cubeL2 ℝ (fun a : Cube n => cubeL2 X
      (fun b : Cube j => f (cubeJoin n j (a,b)))) := by
  simp only [cubeL2, Real.norm_eq_abs, sq_abs]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun b : Cube j =>
    ‖f (cubeJoin n j (_,b))‖ ^ 2) from by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [average_join]

omit [NormedSpace ℝ X] in
theorem cubeL2_comm {n j : ℕ} (f : Cube n → Cube j → X) :
    cubeL2 ℝ (fun a => cubeL2 X (f a)) =
      cubeL2 ℝ (fun b => cubeL2 X (fun a => f a b)) := by
  simp only [cubeL2, Real.norm_eq_abs, sq_abs]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun b => ‖f _ b‖ ^ 2) from by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun a => ‖f a _‖ ^ 2) from by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [average_comm]

theorem vectorWalsh_join {n j : ℕ} (f : Cube (n+j) → X) (a : Cube n) (b : Cube j) :
    vectorWalsh f (cubeJoin n j (a,b)) =
      vectorWalsh (fun d : Cube j => vectorWalsh
        (fun c : Cube n => f (cubeJoin n j (c,d))) a) b := by
  unfold vectorWalsh
  rw [average_join, average_comm]
  simp only [character_join, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  ring

end Cotype

end

end OAI
