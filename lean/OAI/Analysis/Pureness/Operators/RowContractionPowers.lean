import OAI.Analysis.Pureness.Traces.TracelessRowContraction

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem rowFamily_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → A) (b : κ → A)
    (ha : (∑ i, star (a i) * a i) = 1) (hb : (∑ j, star (b j) * b j) = 1) :
    (∑ p : ι × κ, star (a p.1 * b p.2) * (a p.1 * b p.2)) = 1 ∧
      ‖∑ p : ι × κ, (a p.1 * b p.2) * star (a p.1 * b p.2)‖ ≤
        ‖∑ j, b j * star (b j)‖ * ‖∑ i, a i * star (a i)‖ := by
  classical
  constructor
  · calc
      _ = ∑ j, star (b j) * (∑ i, star (a i) * a i) * b j := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
      _ = 1 := by simp only [ha, mul_one, hb]
  · let T := ∑ j, b j * star (b j)
    have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => mul_star_self_nonneg (b j))
    have heq : (∑ p : ι × κ, (a p.1 * b p.2) * star (a p.1 * b p.2)) =
        ∑ i, a i * T * star (a i) := by
      simp only [T, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    have hpos : 0 ≤ ∑ i, a i * T * star (a i) := by
      rw [← heq]
      exact Finset.sum_nonneg (fun p _ => mul_star_self_nonneg _)
    have hbound : (∑ i, a i * T * star (a i)) ≤ ‖T‖ • (∑ i, a i * star (a i)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_le_sum
      intro i _
      simpa only [star_star] using CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := star (a i)) (b := T) hT.isSelfAdjoint
    rw [heq]
    calc
      _ ≤ ‖‖T‖ • (∑ i, a i * star (a i))‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hbound hpos
      _ = _ := by rw [norm_smul, norm_norm]

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteFamily_reindex {ι : Type*} [Fintype ι] (a : ι → A) :
    ∃ (n : ℕ) (b : Fin n → A),
      (∑ i, star (b i) * b i) = ∑ i, star (a i) * a i ∧
      (∑ i, b i * star (b i)) = ∑ i, a i * star (a i) := by
  let e := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun i => a (e i),
    e.sum_comp (fun i => star (a i) * a i), e.sum_comp (fun i => a i * star (a i))⟩

theorem exists_rowFamily_pow {n : ℕ} (a : Fin n → A)
    (ha : (∑ i, star (a i) * a i) = 1) (k : ℕ) :
    ∃ (m : ℕ) (b : Fin m → A), (∑ i, star (b i) * b i) = 1 ∧
      ‖∑ i, b i * star (b i)‖ ≤ ‖∑ i, a i * star (a i)‖ ^ k := by
  induction k with
  | zero =>
      refine ⟨1, fun _ => 1, by simp, ?_⟩
      by_cases h1 : (1 : A) = 0
      · simp [h1]
      · have : Nontrivial A := nontrivial_of_ne 1 0 h1
        simp
  | succ k ih =>
      obtain ⟨m, b, hb, hbn⟩ := ih
      obtain ⟨hcol, hrow⟩ := rowFamily_product a b ha hb
      obtain ⟨q, c, hcc, hcr⟩ := finiteFamily_reindex (fun p : Fin n × Fin m => a p.1 * b p.2)
      refine ⟨q, c, hcc.trans hcol, ?_⟩
      rw [hcr]
      exact hrow.trans (by simpa only [pow_succ] using
        mul_le_mul_of_nonneg_right hbn (norm_nonneg (∑ i, a i * star (a i))))

theorem exists_arbitrarily_small_rowFamily (h : ¬ Nonempty (TracialState A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin n → A), (∑ i, star (a i) * a i) = 1 ∧
      ‖∑ i, a i * star (a i)‖ < ε := by
  obtain ⟨n, a, hcol, hrow⟩ := exists_rowContraction_of_no_tracialState h
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hrow
  obtain ⟨m, b, hb, hbn⟩ := exists_rowFamily_pow a hcol k
  exact ⟨m, b, hb, hbn.trans_lt hk⟩
end CuntzPureness

end

end OAI
