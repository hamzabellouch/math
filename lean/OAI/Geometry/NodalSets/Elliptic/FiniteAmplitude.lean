import OAI.Geometry.NodalSets.Elliptic.UniformPolynomial

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def finiteAmplitude (A : ℕ → CPoly) (J : ℕ) (N : ℝ) : Coord → ℂ :=
  polynomialFamily (fun j : Fin (J + 1) ↦ A j.val)
    (fun t : ℝ ↦ fun j : Fin (J + 1) ↦ (t : ℂ) ^ j.val) N⁻¹

lemma finiteAmplitude_contDiff (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    ContDiff ℝ ∞ (finiteAmplitude A J N) := polynomialFamily_contDiff _ _ _

theorem finiteAmplitude_uniform_derivative_bound (A : ℕ → CPoly) (J k : ℕ) (R : ℝ) :
    ∃ C > 0, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (finiteAmplitude A J N) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := polynomialFamily_uniform_derivative_bound
    (fun j : Fin (J + 1) ↦ A j.val)
    (fun t : ℝ ↦ fun j : Fin (J + 1) ↦ (t : ℂ) ^ j.val)
    (fun j ↦ Complex.continuous_ofReal.pow j.val) (Set.Icc (0 : ℝ) 1) isCompact_Icc R k
  refine ⟨C, hC, ?_⟩
  intro N hN x hx
  apply hb N⁻¹ _ x hx
  constructor
  · exact inv_nonneg.mpr (le_trans zero_le_one hN)
  · exact inv_le_one_of_one_le₀ hN

lemma reval_center (p : CPoly) : reval p 0 = p.coeff 0 := by
  simp [reval, MvPolynomial.constantCoeff_eq]

theorem finiteAmplitude_center (A : ℕ → CPoly) (J : ℕ) (N : ℝ)
    (hA : ∀ j, MvPolynomial.homogeneousComponent 0 (A j) = if j = 0 then 1 else 0) :
    finiteAmplitude A J N 0 = 1 := by
  have hc (j : ℕ) : reval (A j) 0 = if j = 0 then 1 else 0 := by
    have h := congrArg (fun polynomial : CPoly ↦ polynomial.coeff 0) (hA j)
    by_cases hj : j = 0 <;>
      simpa [reval_center, MvPolynomial.coeff_homogeneousComponent, hj] using h
  simp [finiteAmplitude, polynomialFamily, hc, smul_eq_mul, apply_ite]

end
end Yau.Jets

end OAI
