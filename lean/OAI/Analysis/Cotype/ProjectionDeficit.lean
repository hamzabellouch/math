import OAI.Analysis.Cotype.ProjectionProducts
import OAI.Analysis.Cotype.BConvexBlocking

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_norming_sum_deficit {ι : Type*} [Fintype ι]
    (v : ι → X) {R : ℝ} (_hR : 0 ≤ R) (hv : ∀ i, ‖v i‖ ≤ R) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ ∀ i,
      R - ((Fintype.card ι : ℝ)*R-‖∑ j, v j‖) ≤ φ (v i) := by
  classical
  obtain ⟨φ,hφ,he⟩ := exists_dual_vector'' ℝ (∑ j, v j)
  have he' : φ (∑ j, v j) = ‖∑ j, v j‖ := he
  have hb i : φ (v i) ≤ R := by
    apply (le_abs_self _).trans
    exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans (hv i))
  refine ⟨φ,hφ,fun i => ?_⟩
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hb j))
    (Finset.mem_univ i)
  have hs : (∑ j, (R-φ (v j))) = (Fintype.card ι : ℝ)*R-‖∑ j, v j‖ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← map_sum, he']
  rw [hs] at hi
  linarith

theorem abs_prod_sign {n : ℕ} (ε : Cube n) : |∏ i, sign (ε i)| = 1 := by
  rw [Finset.abs_prod]
  have hs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
  simp_rw [hs]
  simp

theorem prod_sign_union_singleton {n : ℕ} (ε : Cube n) (i : Fin n) :
    (∏ j, sign ((!ε j) || decide (j = i))) =
      (∏ j, sign (!ε j)) * sign (ε i) := by
  classical
  have he : (∏ j ∈ Finset.univ.erase i, sign ((!ε j) || decide (j = i))) =
      ∏ j ∈ Finset.univ.erase i, sign (!ε j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), he,
    ← Finset.prod_erase_mul _ (fun j => sign (!ε j)) (Finset.mem_univ i)]
  simp only [decide_true, Bool.or_true, sign_true, sign_not]
  cases ε i <;> norm_num

theorem projection_sign_sum_lower {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hn : ∀ i x, ‖P i x‖ ≤ ‖x‖) (y : X) (ε : Cube n) :
    (n : ℝ)*(‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) ≤
      ‖rademacherSum X (fun i => P i y) ε‖ := by
  classical
  let v : Cube n → X := fun η => (∏ i, sign (η i)) • projectionSubset P η y
  have hv η : ‖v η‖ ≤ ‖y‖ := by
    simpa only [v, norm_smul, Real.norm_eq_abs, abs_prod_sign, one_mul] using
      projectionSubset_norm_apply P hn η y
  have hsum : (∑ η, v η) = projectionProduct (fun i => 1-P i) y := by
    rw [projectionComplement_expansion]
    simp [v]
  obtain ⟨φ,hφ,hφv⟩ := exists_norming_sum_deficit v (norm_nonneg y) hv
  have hcard : (Fintype.card (Cube n) : ℝ) = (2 : ℝ)^n := by
    simp [Cube]
  rw [hcard, hsum] at hφv
  let B : Cube n := fun i => !ε i
  let a : ℝ := ∏ i, sign (B i)
  let z : X := rademacherSum X (fun i => P i y) ε
  have hi i : a * φ (projectionSubset P B (sign (ε i) • P i y)) =
      φ (v (fun j => B j || decide (j = i))) := by
    have hm := projectionSubset_union P hp hc B (fun j => decide (j = i))
    rw [projectionSubset_singleton] at hm
    have hmap : projectionSubset P B (P i y) =
        projectionSubset P (fun j => B j || decide (j = i)) y := by
      exact congrArg (fun T : X →L[ℝ] X => T y) hm
    simp only [map_smul, smul_eq_mul, hmap, v]
    rw [prod_sign_union_singleton ε i]
    dsimp [a, B]
    ring
  have hlow : (n : ℝ)*(‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) ≤
      a * φ (projectionSubset P B z) := by
    dsimp [z, rademacherSum]
    simp only [map_sum, Finset.mul_sum]
    calc
      _ = ∑ _i : Fin n, (‖y‖-((2 : ℝ)^n*‖y‖-‖projectionProduct (fun i => 1-P i) y‖)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [hi]; exact hφv _)
  apply hlow.trans
  calc
    _ ≤ |a * φ (projectionSubset P B z)| := le_abs_self _
    _ = |φ (projectionSubset P B z)| := by rw [abs_mul, show |a|=1 from abs_prod_sign B, one_mul]
    _ ≤ ‖projectionSubset P B z‖ := (φ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hφ)
    _ ≤ ‖z‖ := projectionSubset_norm_apply P hn B z

theorem projection_complement_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i x, ‖P i x‖ ≤ ‖x‖) (y : X) :
    ‖projectionProduct (fun i => 1-P i) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  obtain ⟨ε,hε⟩ := exists_sign_of_radius h (norm_nonneg y) (fun i => P i y) (fun i => hP i y)
  have hl := projection_sign_sum_lower P hp hc hP y ε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ)*(δ/(n : ℝ)) = δ := mul_div_cancel₀ δ (ne_of_gt hnR)
  have he' : (n : ℝ)*(δ/(n : ℝ))*‖y‖ = δ*‖y‖ := by rw [he]
  apply (mul_le_mul_iff_right₀ hnR).mp
  nlinarith [he']

end Cotype

end

end OAI
