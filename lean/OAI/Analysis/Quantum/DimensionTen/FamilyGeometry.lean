import OAI.Analysis.Quantum.DimensionTen.PureMatrices

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma no_two_zero_cover (p q : Fin 20 → ℂ)
    (hp : (Finset.univ.filter (fun k => p k = 0)).card ≤ 9)
    (hq : (Finset.univ.filter (fun k => q k = 0)).card ≤ 9)
    (h : ∀ k, p k = 0 ∨ q k = 0) : False := by
  classical
  have hs : Finset.univ ⊆ (Finset.univ.filter (fun k => p k = 0)) ∪
      (Finset.univ.filter (fun k => q k = 0)) := by
    intro k hk
    simpa using h k
  have hh := Finset.card_le_card hs
  have hu := Finset.card_union_le (Finset.univ.filter (fun k => p k = 0))
    (Finset.univ.filter (fun k => q k = 0))
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  omega

lemma productfree_of_kernel_family (X : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ)
    (hX : X.IsHermitian) (f : Fin 20 → (Fin 10 → ℂ))
    (hpos : ∀ u : Fin 10 → ℂ, u ≠ 0 →
      (Finset.univ.filter (fun k => star u ⬝ᵥ f k = 0)).card ≤ 9)
    (hker : ∀ k, X *ᵥ productVector (f k) (f k) = 0) :
    ∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      X *ᵥ w = productVector u v → u = 0 ∨ v = 0 := by
  intro u v w hw
  by_cases hu : u = 0
  · exact Or.inl hu
  by_cases hv : v = 0
  · exact Or.inr hv
  exfalso
  apply no_two_zero_cover (fun k => star u ⬝ᵥ f k) (fun k => star v ⬝ᵥ f k)
    (hpos u hu) (hpos v hv)
  intro k
  apply mul_eq_zero.mp
  rw [← product_dot, ← hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    hX.eq, hker, dotProduct_zero]

lemma kronecker_mul_product {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    (A ⊗ₖ B) *ᵥ productVector u v = productVector (A *ᵥ u) (B *ᵥ v) := by
  ext ⟨i,j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, productVector,
    Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma kronecker_product_dot {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ ((A ⊗ₖ B) *ᵥ productVector u v) =
      (star u ⬝ᵥ (A *ᵥ u)) * (star v ⬝ᵥ (B *ᵥ v)) := by
  rw [kronecker_mul_product, product_dot]

lemma psd_summand_kernel {r n : Type*} [Fintype r] [Fintype n]
    (A : r → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (v : n → ℂ)
    (hv : (∑ i, A i) *ᵥ v = 0) (i : r) : A i *ᵥ v = 0 := by
  have hs : ∑ j, star v ⬝ᵥ (A j *ᵥ v) = 0 := by
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hv, dotProduct_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset r)) => (hA j).dotProduct_mulVec_nonneg v)).mp hs i
      (Finset.mem_univ i)
  exact (hA i).dotProduct_mulVec_zero_iff.mp hi

lemma matrix_nonzero_row {n : ℕ} {A : Mat n} (hA : A ≠ 0) :
    ∃ i : Fin n, star (A i) ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hA
  ext i j
  have hi := congrFun (hh i) j
  simpa only [Pi.star_apply, Pi.zero_apply, star_eq_zero, Matrix.zero_apply] using hi

lemma nonseparable_of_kernel_family (X : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ)
    (hne : X ≠ 0) (f : Fin 20 → (Fin 10 → ℂ))
    (hpos : ∀ u : Fin 10 → ℂ, u ≠ 0 →
      (Finset.univ.filter (fun k => star u ⬝ᵥ f k = 0)).card ≤ 9)
    (hker : ∀ k, X *ᵥ productVector (f k) (f k) = 0) : ¬ separable X := by
  intro hsep
  obtain ⟨r, A, B, hAB, hsum⟩ := hsep
  have hi (i : Fin r) : A i = 0 ∨ B i = 0 := by
    by_cases hA : A i = 0
    · exact Or.inl hA
    by_cases hB : B i = 0
    · exact Or.inr hB
    exfalso
    obtain ⟨a, ha⟩ := matrix_nonzero_row hA
    obtain ⟨b, hb⟩ := matrix_nonzero_row hB
    apply no_two_zero_cover
      (fun k => star (star (A i a)) ⬝ᵥ f k) (fun k => star (star (B i b)) ⬝ᵥ f k)
      (hpos _ ha) (hpos _ hb)
    intro k
    have hk : (A i ⊗ₖ B i) *ᵥ productVector (f k) (f k) = 0 := by
      apply psd_summand_kernel (fun j => A j ⊗ₖ B j)
        (fun j => (hAB j).1.kronecker (hAB j).2) _ _ i
      simpa only [Matrix.kronecker] using hsum ▸ hker k
    have hd : (star (f k) ⬝ᵥ (A i *ᵥ f k)) * (star (f k) ⬝ᵥ (B i *ᵥ f k)) = 0 := by
      rw [← kronecker_product_dot, hk, dotProduct_zero]
    rcases mul_eq_zero.mp hd with h | h
    · left
      have hz := (hAB i).1.dotProduct_mulVec_zero_iff.mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz a
    · right
      have hz := (hAB i).2.dotProduct_mulVec_zero_iff.mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz b
  apply hne
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i hi'
  rcases hi i with h | h <;> simp [h, Matrix.kronecker]

end DimensionTen

end
end

end OAI
