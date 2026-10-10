import OAI.Probability.SignedSweeps.OrbitDimension

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma coloringOrbit_product {n : ℕ} {I : Type*} (c : Fin n → I) (p : I → ℝ)
    (q : ColoringOrbit c) :
    (∏ x, p (q.1 x)) = ∏ x, p (c x) := by
  obtain ⟨g, hg⟩ := q.property
  rw [← hg]
  exact Equiv.prod_comp g⁻¹ (p ∘ c)

lemma coloringOrbit_card_mul_product_le_one {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (Fintype.card (ColoringOrbit c) : ℝ) * (∏ x, p (c x)) ≤ 1 := by
  classical
  calc
    _ = ∑ q : ColoringOrbit c, ∏ x, p (q.1 x) := by
      simp only [coloringOrbit_product, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ f : Fin n → I, ∏ x, p (f x) := by
      let T := Finset.univ.image (fun q : ColoringOrbit c => q.1)
      have hi : Function.Injective (fun q : ColoringOrbit c => q.1) :=
        fun q r h => Subtype.ext h
      calc
        _ = ∑ f ∈ T, ∏ x, p (f x) := (Finset.sum_image hi.injOn).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f hf hfn => Finset.prod_nonneg (fun x hx => hp (f x)))
    _ = 1 := by rw [← Fintype.sum_pow, hsum, one_pow]

lemma coloringOrbit_card_le_exp {n : ℕ} {I : Type*} [Fintype I]
    (c : Fin n → I) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (Fintype.card (ColoringOrbit c) : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) := by
  have he : (∏ x, p (c x)) = Real.exp (∑ x, Real.log (p (c x))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun x hx => (Real.exp_log (hc x)).symm)
  have h := coloringOrbit_card_mul_product_le_one c p hp hsum
  rw [he] at h
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (∑ x, Real.log (p (c x))))).mp
  simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

lemma finrank_le_coloring_entropy {n : ℕ} {I E A : Type*} [Fintype I]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : ∀ x, 0 < p (c x)) :
    (finrank ℂ E : ℝ) ≤ Real.exp (-(∑ x, Real.log (p (c x)))) * finrank ℂ A := by
  have h := finrank_le_coloringOrbit ρ f hf c hstable
  have h' : (finrank ℂ E : ℝ) ≤ (Fintype.card (ColoringOrbit c) : ℝ) * finrank ℂ A := by
    exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (coloringOrbit_card_le_exp c p hp hsum hc)
    (Nat.cast_nonneg _))

end SignedSweeps
end

end OAI
