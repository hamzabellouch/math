import OAI.NumberTheory.Ostmann.Construction.SmoothCellDeletion
import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

/-! # Matching the actual deleted smooth cell priors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothCellRoleFactor (E : Finset ℕ) (φ : ℝ → ℝ)
    (G : ℝ) (p : ℕ) : ℝ :=
  if p ∈ E then 0 else φ (Real.log p - G)

theorem smoothCellRoleFactor_mem_Icc (E : Finset ℕ) (φ : ℝ → ℝ)
    (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) (G : ℝ) (p : ℕ) :
    smoothCellRoleFactor E φ G p ∈ Set.Icc (0 : ℝ) 1 := by
  unfold smoothCellRoleFactor
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact hφ _

theorem deletedSmoothCellPrior_factor (P E : Finset ℕ) (φ : ℝ → ℝ)
    (G : ℝ) (p : P) :
    deletedSmoothCellPrior P E φ G p =
      Real.exp (smoothGiantLogNormalizer (P \ E) φ G) * (p : ℝ)⁻¹ *
        smoothCellRoleFactor E φ G p := by
  unfold deletedSmoothCellPrior smoothCellRoleFactor
  split_ifs <;> ring

/-- A matched counterpart retains its exact smooth unary factors. Only its
normalizing constants and reciprocal product are extracted. -/
theorem finite_matched_smooth_prior {I : Type*} [Fintype I]
    (P : Finset ℕ) (E : I → Finset ℕ) (φ : ℝ → ℝ) (G : I → ℝ)
    (e : Equiv.Perm I) (x : I → P) :
    (∏ i, deletedSmoothCellPrior P (E i) φ (G i) (x (e i))) =
      Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) *
        (∏ i, (x i : ℝ))⁻¹ *
          ∏ i, smoothCellRoleFactor (E (e.symm i)) φ (G (e.symm i)) (x i) := by
  simp_rw [deletedSmoothCellPrior_factor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Real.exp_sum, Equiv.prod_comp e (fun i => (x i : ℝ)⁻¹)]
  have hf : (∏ i, smoothCellRoleFactor (E i) φ (G i) (x (e i))) =
      ∏ i, smoothCellRoleFactor (E (e.symm i)) φ (G (e.symm i)) (x i) := by
    simpa only [e.symm_apply_apply] using Equiv.prod_comp e
      (fun i => smoothCellRoleFactor (E (e.symm i)) φ (G (e.symm i)) (x i))
  rw [hf, Finset.prod_inv_distrib]

/-- Every original smooth tuple atom has the reciprocal product bound used
in the arrangement diagonal. The priors may have different cell centers. -/
theorem smooth_tuple_point_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) (E : I → Finset ℕ) (φ : ℝ → ℝ)
    (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) (G : I → ℝ) (x : I → P) :
    (∏ i, deletedSmoothCellPrior P (E i) φ (G i) (x i)) ≤
      Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) *
        (∏ i, (x i : ℝ))⁻¹ := by
  have he : (∏ i, deletedSmoothCellPrior P (E i) φ (G i) (x i)) =
      Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) *
        (∏ i, (x i : ℝ))⁻¹ * ∏ i, smoothCellRoleFactor (E i) φ (G i) (x i) := by
    simpa only [Equiv.refl_symm, Equiv.refl_apply] using
      finite_matched_smooth_prior P E φ G (Equiv.refl I) x
  rw [he]
  apply mul_le_of_le_one_right (by positivity)
  exact Finset.prod_le_one₀
    (fun i _ => (smoothCellRoleFactor_mem_Icc _ φ hφ _ _).1)
    (fun i _ => (smoothCellRoleFactor_mem_Icc _ φ hφ _ _).2)

/-- The ordered prime-product fibre costs only a factorial, while the
original smooth counterpart supplies its reciprocal total product. -/
theorem smooth_distinct_product_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (E : Fin n → Finset ℕ) (φ : ℝ → ℝ)
    (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) (G : Fin n → ℝ)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x) (M : ℕ) :
    (∑ x ∈ S.filter (fun x => (∏ i, (x i : ℕ)) = M),
      ∏ i, deletedSmoothCellPrior P (E i) φ (G i) (x i)) ≤
      (n.factorial : ℝ) *
        Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) * (M : ℝ)⁻¹ := by
  let T := S.filter (fun x => (∏ i, (x i : ℕ)) = M)
  have hc : T.card ≤ n.factorial := by
    apply (Finset.card_le_card (show T ⊆ Finset.univ.filter
      (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M) from ?_)).trans
      (card_distinct_prime_product_fiber P hP n M)
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hxS, hxM⟩
  calc
    _ ≤ ∑ _x ∈ T, Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) *
        (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2
      simpa only [he] using smooth_tuple_point_bound P E φ hφ G x
    _ = (T.card : ℝ) * (Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) *
        (M : ℝ)⁻¹) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hc : (T.card : ℝ) ≤ n.factorial) (by positivity :
          0 ≤ Real.exp (∑ i, smoothGiantLogNormalizer (P \ E i) φ (G i)) * (M : ℝ)⁻¹)

end Ostmann

end OAI
