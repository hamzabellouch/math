import OAI.Analysis.OperatorAlgebra.TracialSpatialApproximation
import OAI.Analysis.OperatorAlgebra.DensityUnitaryCoefficients

namespace OAI

/-! Product-state approximation from the finite tracial vector construction. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace WeakPureInfiniteness

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I]

lemma tracial_product_error_lt (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (a : M.toStarSubalgebra) (u : unitary M.toStarSubalgebra)
    (z : NuclearUltrapower.HilbertSchmidt H) (hzn : ‖z‖ = 1)
    {D δ ε : ℝ} (hD : ‖a‖ + 1 ≤ D) (hδ : 0 ≤ δ) (hsmall : D * δ < ε)
    (htrace : ‖τ.functional (a * (u : M.toStarSubalgebra)) - inner ℂ z
      (densityLeftRepresentation ((a * (u : M.toStarSubalgebra)) : H →L[ℂ] H) z)‖ < δ)
    (hcent : ‖hsLeftUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra u) z -
      hsRightUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra u) z‖ < δ) :
    ‖inner ℂ z ((densityLeftRepresentation (a : H →L[ℂ] H) *
      densityRightRepresentation (MulOpposite.op ((u : M.toStarSubalgebra) : H →L[ℂ] H))) z) -
      τ.functional (a * (u : M.toStarSubalgebra))‖ < ε := by
  let U := subalgebraUnitaryIsometry M.toStarSubalgebra u
  have hb := density_unitary_product_error (H := H) (a : H →L[ℂ] H) U z hzn
    (τ.functional (a * (u : M.toStarSubalgebra)))
  have hn : ‖densityLeftRepresentation (a : H →L[ℂ] H)‖ ≤ ‖a‖ :=
    NonUnitalStarAlgHom.norm_apply_le (densityLeftRepresentation (H := H)).toNonUnitalStarAlgHom _
  rw [norm_sub_rev] at htrace
  apply hb.trans_lt
  apply lt_of_lt_of_le _ (le_of_lt hsmall)
  have h₁ := add_lt_add_of_le_of_lt
    (mul_le_mul_of_nonneg_left hcent.le (norm_nonneg (densityLeftRepresentation (a : H →L[ℂ] H)))) htrace
  refine h₁.trans_le ?_
  calc
    ‖densityLeftRepresentation (a : H →L[ℂ] H)‖ * δ + δ ≤ ‖a‖ * δ + δ :=
      add_le_add (mul_le_mul_of_nonneg_right hn hδ) (le_refl δ)
    _ = (‖a‖ + 1) * δ := by ring
    _ ≤ D * δ := mul_le_mul_of_nonneg_right hD hδ

/-- A finite family of diagonal trace coefficients is approximated by
coefficients of the genuine spatial left/right representation. -/
theorem expectation_spatial_product_approximation (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → M.toStarSubalgebra) (u : I → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : NuclearUltrapower.HilbertSchmidt H, ‖z‖ = 1 ∧
      0 ≤ NuclearUltrapower.hsOperator z ∧
      (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
        ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
      ∀ i, ‖inner ℂ z ((densityLeftRepresentation (a i : H →L[ℂ] H) *
        densityRightRepresentation (MulOpposite.op ((u i : M.toStarSubalgebra) : H →L[ℂ] H))) z) -
          τ.functional (a i * (u i : M.toStarSubalgebra))‖ < ε := by
  classical
  let D : ℝ := 1 + ∑ i, ‖a i‖
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let δ : ℝ := ε / (2 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨z, hzn, hzp, hzf, hza, hzu⟩ := expectation_complex_spatial_approximation
    M τ E hE hEr hEf (fun i => a i * (u i : M.toStarSubalgebra)) u hδ
  have hsmall : D * δ < ε := by
    have hd : D * δ = ε / 2 := by
      dsimp only [δ]
      field_simp [hD0.ne']
    rw [hd]
    exact half_lt_self hε
  refine ⟨z, hzn, hzp, hzf, ?_⟩
  intro i
  have hi : ‖a i‖ + 1 ≤ D := by
    have hh := Finset.single_le_sum (f := fun j : I => ‖a j‖)
      (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
    dsimp only [D]
    linarith
  exact tracial_product_error_lt M τ (a i) (u i) z hzn hi hδ.le hsmall (hza i) (hzu i)

end WeakPureInfiniteness

end

end OAI
