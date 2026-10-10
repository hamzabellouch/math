import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

def momentBudget (ε K t : ℝ) : ℝ := ε*Real.exp (K*t)

def budgetSlope (N : ℕ) (η : ℝ) : ℝ := ((N:ℝ)+1)^2*(1+2/η)

lemma budgetSlope_ge_one (N : ℕ) {η : ℝ} (hη : 0<η) : 1 ≤ budgetSlope N η := by
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hd : 0 ≤ 2/η := by positivity
  have h1 : 1 ≤ ((N:ℝ)+1)^2 := by nlinarith
  exact (one_mul (1:ℝ)).symm ▸ mul_le_mul h1 (by linarith : 1 ≤ 1+2/η)
    (by norm_num) (by positivity)

lemma momentBudget_nonneg {ε : ℝ} (hε : 0 ≤ ε) (K t : ℝ) : 0 ≤ momentBudget ε K t :=
  mul_nonneg hε (Real.exp_pos _).le

lemma le_momentBudget {ε K t : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    ε ≤ momentBudget ε K t := by
  exact le_mul_of_one_le_right hε (Real.one_le_exp (mul_nonneg hK ht))

lemma momentBudget_step {ε K t q : ℝ} (hε : 0 ≤ ε) :
    momentBudget ε K t+K*momentBudget ε K t*q ≤ momentBudget ε K (t+q) := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (K*q))
    (momentBudget_nonneg hε K t)
  calc
    _=momentBudget ε K t*(K*q+1) := by ring
    _ ≤ momentBudget ε K t*Real.exp (K*q) := hh
    _=momentBudget ε K (t+q) := by simp only [momentBudget,mul_add,Real.exp_add,mul_assoc]

lemma word_momentBudget_step {ε η t q : ℝ} (hε : 0 ≤ ε) (hη : 0<η)
    (ht : 0 ≤ t) (hq : 0 ≤ q) {n N : ℕ} (hn : n ≤ N) :
    momentBudget ε (budgetSlope N η) t+
      ((n:ℝ)+(n:ℝ)^2)*(ε+2*momentBudget ε (budgetSlope N η) t/η)*q ≤
      momentBudget ε (budgetSlope N η) (t+q) := by
  let B := momentBudget ε (budgetSlope N η) t
  have hB : 0 ≤ B := momentBudget_nonneg hε _ _
  have hK : 0 ≤ budgetSlope N η := (by norm_num : (0:ℝ) ≤ 1).trans (budgetSlope_ge_one N hη)
  have hεB : ε ≤ B := le_momentBudget hε hK ht
  have hn' : (n:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr hn
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hf : (n:ℝ)+(n:ℝ)^2 ≤ ((N:ℝ)+1)^2 := by nlinarith
  have hd : ε+2*B/η ≤ (1+2/η)*B := by
    calc
      _ ≤ B+2*B/η := add_le_add hεB le_rfl
      _=_ := by ring
  have hh : ((n:ℝ)+(n:ℝ)^2)*(ε+2*B/η) ≤ budgetSlope N η*B := by
    calc
      _ ≤ ((N:ℝ)+1)^2*((1+2/η)*B) := mul_le_mul hf hd (by positivity) (by positivity)
      _=_ := by dsimp [budgetSlope]; ring
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hq)).trans (momentBudget_step hε)

lemma pure_momentBudget_step {ε η t q : ℝ} (hε : 0 ≤ ε) (hη : 0<η)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (N : ℕ) :
    momentBudget ε (budgetSlope N η) t+ε*q ≤ momentBudget ε (budgetSlope N η) (t+q) := by
  have hK := budgetSlope_ge_one N hη
  have hB := momentBudget_nonneg hε (budgetSlope N η) t
  have hεB := le_momentBudget hε ((by norm_num : (0:ℝ) ≤ 1).trans hK) ht
  have hh : ε ≤ budgetSlope N η*momentBudget ε (budgetSlope N η) t :=
    hεB.trans (le_mul_of_one_le_left hB hK)
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hq)).trans (momentBudget_step hε)

end Kadison.FinitePatching

end

end
end

end OAI
