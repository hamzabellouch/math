import OAI.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [IsEmpty σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realPolynomialSymbolHom_eq_one_of_isEmpty (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF w g = 1 := by
  apply NilpotentLieBCHGroup.ext
  change F.realPolynomialSymbolMap b ω hF w g.coord = 0
  rw [F.realPolynomialSymbolMap_eq_zero_iff,
    F.realification.polynomialSymbolMap_eq_zero_iff]
  intro α
  have hα : α = 0 := Subsingleton.elim _ _
  rw [hα, map_zero, zero_add, F.realification.one_eq_top]
  exact Submodule.mem_top

theorem hasCommonRefilteredOrbitFactors_of_isEmpty (side : σ → ℝ) (q : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q 1 ⊥ g := by
  refine ⟨1, g, 1, by simp only [one_mul, mul_one], ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro t
    rw [F.realPolynomialSymbolHom_eq_one_of_isEmpty b ω hF]
    change eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ : σ => 1) 0) ∈
      realificationLieSubalgebra (⊥ : LieSubalgebra ℚ F.AssociatedGraded)
    rw [map_zero, map_zero]
    exact zero_mem _
  · intro α i
    change |(b.baseChange ℝ).repr
      (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ _
    simp only [map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg (Real.exp_nonneg q)
      (monomialScale_pos side (fun i => isEmptyElim i) α).le
  · refine ⟨fun _ => 0, ?_⟩
    funext z
    simp only [NilpotentLieBCHGroup.coord_one, ZeroMemClass.coe_zero, map_zero,
      Finsupp.zero_apply, Pi.smul_apply, smul_eq_mul, mul_zero, Int.cast_zero]
  · change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
    simp only [map_zero, Finsupp.zero_apply]
  · change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
    simp only [map_zero, Finsupp.zero_apply]

theorem gradedRefiltrationLayer_bot_top :
    F.gradedRefiltrationLayer (⊥ : LieSubalgebra ℚ F.AssociatedGraded) s = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨hxF, hx0⟩ := (F.mem_gradedRefiltrationLayer ⊥ s x).mp hx
  have hnext := (F.associatedGradedPieceMap_eq_zero_iff s ⟨x, hxF⟩).mp
    ((LieSubalgebra.mem_bot _).mp hx0)
  simpa only [F.terminal] using hnext

theorem realGradedRefiltrationLayer_bot_top :
    F.realGradedRefiltrationLayer (⊥ : LieSubalgebra ℚ F.AssociatedGraded) s = ⊥ := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_bot_top,
    Submodule.baseChange_bot]

end Erdos3.NilpotentLieFiltration

end

end OAI
