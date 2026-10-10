import OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

theorem sum_pow_fin_le_inv_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (N : ℕ) : (∑ k : Fin N, s ^ (k : ℕ)) ≤ (1 - s)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s ^ k), ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hs1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hs0 N)

theorem sum_pow_degree_assignments_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) =
      (∑ k : Fin N, s ^ (k : ℕ)) ^ Fintype.card ι := by
  classical
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin N) => s ^ (k : ℕ))]
  simp

theorem sum_pow_degree_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) ≤
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  rw [sum_pow_degree_assignments_eq]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hs0 _)
    (sum_pow_fin_le_inv_one_sub hs0 hs1 N) _

theorem collision_geometric_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (ι → Fin N)).filter
        (fun f => Function.Injective (fun i => (group i, (f i : ℕ)))),
      (s * s) ^ (∑ i, (f i : ℕ))) ≤
      s ^ (∑ a, (multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let C := ∑ a, (multiplicity Finset.univ group a).choose 2
  have hpoint : ∀ f ∈ good,
      (s * s) ^ (∑ i, (f i : ℕ)) ≤ s ^ C * s ^ (∑ i, (f i : ℕ)) := by
    intro f hf
    have hinj := (Finset.mem_filter.mp hf).2
    have hdeg : C ≤ ∑ i, (f i : ℕ) :=
      sum_choose_multiplicity_le_sum_degree_univ group (fun i => (f i : ℕ)) hinj
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1.le hdeg)
      (pow_nonneg hs0 _)
  calc
    _ ≤ ∑ f ∈ good, s ^ C * s ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum hpoint
    _ = s ^ C * ∑ f ∈ good, s ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ s ^ C * ∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro f _ _
      exact pow_nonneg hs0 _
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pow_degree_assignments_le hs0 hs1 N)
      (pow_nonneg hs0 C)

end PiExponent.Collision

end OAI
