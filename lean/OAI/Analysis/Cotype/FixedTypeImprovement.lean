import OAI.Analysis.Cotype.BConvexQuantitative

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem sum_sq_le_card_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i)^2 ≤ (s.card : ℝ)*∑ i ∈ s, (a i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a

omit [NormedSpace ℝ X] in

theorem sum_norm_sq_le_of_short_coordinate {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (hx : ∑ i, ‖x i‖^2 = 1)
    (i : Fin n) (hi : ‖x i‖ ≤ 1/(4*(n : ℝ))) :
    (∑ j, ‖x j‖)^2 ≤ (n : ℝ)-1/2 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxi j : ‖x j‖ ≤ 1 := by
    have hsq := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖x k‖)
      (Finset.mem_univ j)
    rw [hx] at hsq
    nlinarith [norm_nonneg (x j)]
  have hsum : (∑ j, ‖x j‖) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hxi j)
      _ = _ := by simp
  have herase : (Finset.univ.erase i : Finset (Fin n)).card = n-1 := by simp
  have hn1 : (n-1 : ℕ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hcs := sum_sq_le_card_sum_sq (Finset.univ.erase i) (fun j => ‖x j‖)
  rw [herase,hn1] at hcs
  have hs := Finset.sum_erase_add Finset.univ (fun j => ‖x j‖) (Finset.mem_univ i)
  have hs2 := Finset.sum_erase_add Finset.univ (fun j => ‖x j‖^2) (Finset.mem_univ i)
  rw [hx] at hs2
  rw [show (∑ j ∈ Finset.univ.erase i, ‖x j‖) = (∑ j, ‖x j‖)-‖x i‖ by linarith,
    show (∑ j ∈ Finset.univ.erase i, ‖x j‖^2) = 1-‖x i‖^2 by linarith] at hcs
  have hsmall : ‖x i‖ * (n : ℝ) ≤ 1/4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4*n)).mp hi
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsum (norm_nonneg (x i))
  have hnsq : 0 ≤ (n : ℝ)*‖x i‖^2 := mul_nonneg hn0.le (sq_nonneg _)
  nlinarith

theorem exists_normalized_quadratic_gap {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (hδ : 0 < δ)
    (h : ∀ y : Fin n → X, (∀ i, ‖y i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X y ε‖ ≤ (n : ℝ)-δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : Fin n → X, (∑ i, ‖x i‖^2 = 1) →
      cubeL2 X (rademacherSum X x)^2 ≤ (n : ℝ)-η := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let m : ℝ := 1/(4*(n : ℝ))
  let η : ℝ := min (1/2) ((Fintype.card (Cube n) : ℝ)⁻¹*(m*δ)^2)
  have hm : 0 < m := by dsimp [m]; positivity
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min (by norm_num)
    exact mul_pos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos)) (sq_pos_of_pos (mul_pos hm hδ))
  refine ⟨η,hη,fun x hx => ?_⟩
  by_cases hshort : ∃ i, ‖x i‖ ≤ m
  · obtain ⟨i,hi⟩ := hshort
    have hs := sum_norm_sq_le_of_short_coordinate hn x hx i hi
    have hsum0 : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hb := cubeL2_bound hsum0 (norm_rademacherSum_le_sum_norm x)
    have hηhalf : η ≤ 1/2 := min_le_left _ _
    nlinarith [cubeL2_nonneg (rademacherSum X x)]
  · push Not at hshort
    have hb := rademacher_sq_le_of_sign_deficit hδ.le h x hm.le (fun i => (hshort i).le)
    have hcs : (∑ i, ‖x i‖)^2 ≤ (n : ℝ) := by
      simpa [hx] using sum_sq_le_card_sum_sq Finset.univ (fun i => ‖x i‖)
    have hηloss : η ≤ (Fintype.card (Cube n) : ℝ)⁻¹*(m*δ)^2 := min_le_right _ _
    linarith

theorem quadratic_bound_of_normalized {n : ℕ} {A : ℝ}
    (h : ∀ x : Fin n → X, (∑ i, ‖x i‖^2 = 1) →
      cubeL2 X (rademacherSum X x)^2 ≤ A) :
    ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  classical
  intro x
  let S : ℝ := ∑ i, ‖x i‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : S = 0
  · have hx : ∀ i, x i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖x j‖)
        (Finset.mem_univ i)
      change ‖x i‖^2 ≤ S at hi
      rw [hz] at hi
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])
    simp [rademacherSum,hx,cubeL2,average]
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  let r := Real.sqrt S
  have hr : 0 < r := Real.sqrt_pos.mpr hS0
  have hr2 : r^2 = S := Real.sq_sqrt hS
  let y : Fin n → X := fun i => r⁻¹ • x i
  have hy : ∑ i, ‖y i‖^2 = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hr.le),mul_pow,
      ← Finset.mul_sum]
    change (r⁻¹)^2*S = 1
    rw [← hr2,← mul_pow,inv_mul_cancel₀ (ne_of_gt hr)]; norm_num
  have he : rademacherSum X y = fun ε => r⁻¹ • rademacherSum X x ε := by
    funext ε
    simp only [y,rademacherSum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have hh := h y hy
  rw [he,cubeL2_smul,abs_of_nonneg (inv_nonneg.mpr hr.le),mul_pow] at hh
  have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
  have heq : r^2*((r⁻¹)^2*cubeL2 X (rademacherSum X x)^2) =
      cubeL2 X (rademacherSum X x)^2 := by
    rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (ne_of_gt hr),one_pow,one_mul]
  rw [heq,hr2] at hp
  simpa [S,mul_comm] using hp

theorem fixed_quadratic_improvement_of_bConvex (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : ℝ, 0 ≤ A ∧ A < n ∧
      ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  obtain ⟨n,hn,δ,hδ,h⟩ := h
  obtain ⟨η,hη,hηbound⟩ := exists_normalized_quadratic_gap hn hδ h
  let A := max 0 ((n : ℝ)-η)
  have hA : (n : ℝ)-η ≤ A := le_max_right _ _
  refine ⟨n,hn,A,le_max_left _ _,?_,quadratic_bound_of_normalized (fun x hx => (hηbound x hx).trans hA)⟩
  exact max_lt (by exact_mod_cast hn) (by linarith)

end Cotype

end

end OAI
