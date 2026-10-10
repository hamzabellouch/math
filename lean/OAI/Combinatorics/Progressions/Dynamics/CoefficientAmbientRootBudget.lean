import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K]

omit [Fintype K] in
theorem boundedSiteMatrix_norm_le (h : ℕ) (root : K → ℤ) {S : ℝ}
    (hS : 1 ≤ S) (hroot : ∀ k, |(root k : ℝ)| ≤ S)
    (e : BoundedCoefficientExponent K h) :
    ‖boundedSiteMatrix h (fun _ : Unit => root) () e‖ ≤ S ^ h := by
  calc
    _ = ∏ k ∈ e.val.support, |(root k : ℝ)| ^ e.val k := by
      simp only [boundedSiteMatrix, Finsupp.prod, Int.norm_eq_abs, Int.cast_prod,
        Int.cast_pow, Finset.abs_prod, abs_pow]
    _ ≤ ∏ k ∈ e.val.support, S ^ e.val k := by
      apply Finset.prod_le_prod₀
      · intro k _; positivity
      · intro k _; exact pow_le_pow_left₀ (abs_nonneg _) (hroot k) _
    _ = S ^ e.val.degree := by rw [Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]
    _ ≤ S ^ h := pow_le_pow_right₀ hS e.property

theorem coefficientAmbientRootLip_le (m : ℕ) (root : K → ℤ) {S : ℝ}
    (hS : 1 ≤ S) (hroot : ∀ k, |(root k : ℝ)| ≤ S) :
    (coefficientAmbientRootLip m root : ℝ) ≤
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) * S ^ m := by
  simp only [coefficientAmbientRootLip, NNReal.coe_sum, coe_nnnorm]
  calc
    _ ≤ ∑ j : Fin m, ∑ _e : BoundedCoefficientExponent K (j.val + 1), S ^ m := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro e _
      exact (boundedSiteMatrix_norm_le (j.val + 1) root hS hroot e).trans
        (pow_le_pow_right₀ hS (Nat.succ_le_of_lt j.isLt))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_mul]

theorem coefficientAmbientRootLip_allocated_le {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {α : Type*} [Fintype α] (c : LayerSamplerVariables G I n B → ℤ)
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)) :
    (coefficientAmbientRootLip m (allocatedPhysicalCubeRoot B U b S c x y) : ℝ) ≤
      (∑ j : Fin m, (Fintype.card
        (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)) *
      (allocatedPhysicalEntryBudget B U b S c) ^ m :=
  coefficientAmbientRootLip_le m _ (allocatedPhysicalEntryBudget_one_le B U b S c)
    (allocatedPhysicalCube_root_entry_bound B U b S c x y)

end Erdos3.VectorPolynomial

end

end OAI
