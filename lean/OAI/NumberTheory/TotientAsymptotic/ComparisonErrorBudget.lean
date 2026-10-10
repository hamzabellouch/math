import OAI.NumberTheory.TotientAsymptotic.CollisionGridScale
import OAI.NumberTheory.TotientAsymptotic.CollisionSlack

namespace OAI

/-! Explicit rounding and normality errors fit inside the strict-slack saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collisionMesh_eq_sqrt_ratio {x y : ℝ} {i : ℕ}
    (hS : 0 ≤ B (normalityScale x i)) :
    collisionMesh x y i=Real.sqrt (B (normalityScale x i)/B y) := by
  rw [collisionMesh,Real.sqrt_mul hS,Real.sqrt_div hS,mul_div_assoc,Real.sqrt_div_self]
  rfl

lemma sum_a_le_square (b : ℕ) : (∑ j ∈ Finset.Icc 1 b, a j) ≤ (b : ℝ)^2 := by
  rw [sum_a_Icc]
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hl : Real.log (b+1 : ℝ) ≤ b := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < b+1)
  have hh := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ b+1 by positivity)
  nlinarith

lemma comparison_log_sum_bound {b h : ℕ} (hbh : b ≤ h) (hh : 1 ≤ h) :
    (∑ j ∈ Finset.Icc 2 b, ((j : ℝ)*Real.log j+j)) ≤ 2*(h : ℝ)^3 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hcount : (Finset.Icc 2 b).card ≤ h := by
    simp only [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 2 b, 2*(h : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hj).2.trans hbh
      have hl := Real.log_le_self hj0
      have hp := mul_le_mul_of_nonneg_left hl hj0
      nlinarith [sq_nonneg ((h : ℝ)-j)]
    _ = ((Finset.Icc 2 b).card : ℝ)*(2*(h : ℝ)^2) := by simp
    _ ≤ (h : ℝ)*(2*(h : ℝ)^2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcount) (by positivity)
    _ = _ := by ring

lemma grid_error_polynomial_bound {b h : ℕ} {δ : ℝ}
    (hbh : b ≤ h) (hh : 1 ≤ h) (hδ : 0 ≤ δ) :
    ((2*(b : ℝ)+3)*δ)*(∑ j ∈ Finset.Icc 1 b, a j)+
      2*b*((2*(b : ℝ)+3)*δ)+δ*(∑ j ∈ Finset.Icc 2 b, ((j : ℝ)*Real.log j+j)) ≤
      20*(h : ℝ)^3*δ := by
  have hbhR : (b : ℝ) ≤ h := by exact_mod_cast hbh
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hs0 : 0 ≤ ∑ j ∈ Finset.Icc 1 b, a j := Finset.sum_nonneg (fun j hj =>
    (a_pos (Finset.mem_Icc.mp hj).1).le)
  have hsa : (∑ j ∈ Finset.Icc 1 b, a j) ≤ (h : ℝ)^2 :=
    (sum_a_le_square b).trans (pow_le_pow_left₀ hb0 hbhR 2)
  have he : (2*(b : ℝ)+3)*δ ≤ 5*h*δ := mul_le_mul_of_nonneg_right (by linarith) hδ
  have he0 : 0 ≤ (2*(b : ℝ)+3)*δ := by positivity
  have h1 := mul_le_mul he hsa hs0 (by positivity : (0 : ℝ) ≤ 5*h*δ)
  have h2 : 2*b*((2*(b : ℝ)+3)*δ) ≤ 10*(h : ℝ)^2*δ := by
    have hh := mul_le_mul (show 2*(b : ℝ) ≤ 2*h by linarith) he he0
      (by positivity : (0 : ℝ) ≤ 2*h)
    nlinarith [hh]
  have h3 := mul_le_mul_of_nonneg_left (comparison_log_sum_bound hbh hh) hδ
  have hpow : (h : ℝ)^2 ≤ (h : ℝ)^3 := by nlinarith
  have hpowδ := mul_le_mul_of_nonneg_right hpow hδ
  nlinarith

/-- The exponent loss from the paired grid and normality consumes at most a
quarter of the available `h⁻⁴` strict slack. -/
theorem comparison_grid_error_absorbed {b h : ℕ} {δ : ℝ}
    (hbh : b ≤ h) (hh : 2 ≤ h) (hδ : 0 ≤ δ) (hδu : δ ≤ 2/(h : ℝ)^32) :
    ((2*(b : ℝ)+3)*δ)*(∑ j ∈ Finset.Icc 1 b, a j)+
      2*b*((2*(b : ℝ)+3)*δ)+δ*(∑ j ∈ Finset.Icc 2 b, ((j : ℝ)*Real.log j+j)) ≤
      1/(4*(h : ℝ)^4) := by
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := by linarith
  apply (grid_error_polynomial_bound hbh (by omega) hδ).trans
  calc
    _ ≤ 20*(h : ℝ)^3*(2/(h : ℝ)^32) := mul_le_mul_of_nonneg_left hδu (by positivity)
    _ = 40/(h : ℝ)^29 := by field_simp; ring
    _ ≤ _ := by
      have hp : (160 : ℝ) ≤ (h : ℝ)^25 := by
        have h8 : (2 : ℝ)^8 ≤ (h : ℝ)^8 := pow_le_pow_left₀ (by norm_num) hhR 8
        have hbig := pow_le_pow_right₀ (show (1 : ℝ) ≤ h by linarith) (show 8 ≤ 25 by omega)
        norm_num at h8
        linarith
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (h : ℝ)^29)
        (by positivity : (0 : ℝ) < 4*(h : ℝ)^4)).mpr
      have hh := mul_le_mul_of_nonneg_right hp (pow_nonneg h0.le 4)
      convert hh using 1 <;> ring

end TotientAsymptotic

end

end OAI
