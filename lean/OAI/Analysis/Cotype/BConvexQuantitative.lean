import OAI.Analysis.Cotype.BConvexity

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_rademacherSum_le_sum_norm {n : ℕ} (x : Fin n → X) (ε : Cube n) :
    ‖rademacherSum X x ε‖ ≤ ∑ i, ‖x i‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  cases ε i <;> simp

theorem exists_sign_norm_le_sum_sub {n : ℕ} {δ : ℝ}
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (x : Fin n → X) {m : ℝ} (hm : 0 ≤ m) (hmx : ∀ i, m ≤ ‖x i‖) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (∑ i, ‖x i‖)-m*δ := by
  classical
  let y : Fin n → X := fun i => ‖x i‖⁻¹ • x i
  have hy i : ‖y i‖ ≤ 1 := by
    by_cases hz : x i = 0
    · simp [y,hz]
    · simp only [y,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      exact le_refl 1
  have hxy i : ‖x i‖ • y i = x i := by
    by_cases hz : x i = 0
    · simp [y,hz]
    · simp [y,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]
  obtain ⟨ε,hε⟩ := h y hy
  refine ⟨ε,?_⟩
  have he : rademacherSum X x ε = m • rademacherSum X y ε +
      ∑ i, sign (ε i) • ((‖x i‖-m) • y i) := by
    simp only [rademacherSum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm m,← smul_add,← add_smul,add_sub_cancel, hxy]
  have hr : ‖∑ i, sign (ε i) • ((‖x i‖-m) • y i)‖ ≤ ∑ i, (‖x i‖-m) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hb : ‖(‖x i‖-m) • y i‖ ≤ ‖x i‖-m := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hmx i))]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (hmx i)) (hy i)
    cases ε i <;> simpa using hb
  rw [he]
  calc
    _ ≤ ‖m • rademacherSum X y ε‖ + ‖∑ i, sign (ε i) • ((‖x i‖-m) • y i)‖ := norm_add_le _ _
    _ ≤ m*((n : ℝ)-δ) + ∑ i, (‖x i‖-m) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
      exact add_le_add (mul_le_mul_of_nonneg_left hε hm) hr
    _ = _ := by simp [Finset.sum_sub_distrib]; ring

omit [NormedSpace ℝ X] in

theorem average_sq_le_of_one_deficit {n : ℕ} (f : Cube n → X) {S D : ℝ}
    (hD : 0 ≤ D) (hS : ∀ ε, ‖f ε‖ ≤ S)
    (ε : Cube n) (hε : ‖f ε‖ ≤ S-D) :
    average (fun u => ‖f u‖^2) ≤ S^2 - (Fintype.card (Cube n) : ℝ)⁻¹ * D^2 := by
  classical
  have hS0 : 0 ≤ S := (norm_nonneg (f ε)).trans (hS ε)
  have hd u : 0 ≤ S^2-‖f u‖^2 := by nlinarith [hS u,norm_nonneg (f u)]
  have he : D^2 ≤ S^2-‖f ε‖^2 := by nlinarith [norm_nonneg (f ε)]
  have hs := he.trans (Finset.single_le_sum (fun u _ => hd u) (Finset.mem_univ ε))
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Cube n)) : (0 : ℝ) ≤ _))
  have hid : (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, (S^2-‖f u‖^2) =
      S^2-average (fun u => ‖f u‖^2) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      average,smul_eq_mul,mul_sub,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rw [hid] at hh
  linarith

theorem rademacher_sq_le_of_sign_deficit {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ)
    (x : Fin n → X) {m : ℝ} (hm : 0 ≤ m) (hmx : ∀ i, m ≤ ‖x i‖) :
    cubeL2 X (rademacherSum X x)^2 ≤ (∑ i, ‖x i‖)^2 -
      (Fintype.card (Cube n) : ℝ)⁻¹ * (m*δ)^2 := by
  obtain ⟨ε,hε⟩ := exists_sign_norm_le_sum_sub h x hm hmx
  rw [cubeL2_sq]
  exact average_sq_le_of_one_deficit _ (mul_nonneg hm hδ)
    (norm_rademacherSum_le_sum_norm x) ε hε

end Cotype

end

end OAI
