import OAI.Probability.SignedSweeps.MarkedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module
variable {G E : Type*} [Group G] [Fintype G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma matrixCoefficient_basis_inner_sum (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x y : E) :
    ∑ i : Fin (finrank ℂ E), inner ℂ (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x)
      (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) y) =
        (Fintype.card G : ℂ) * inner ℂ x y := by
  simp only [PiLp.inner_apply, matrixCoefficient_apply, RCLike.inner_apply]
  rw [Finset.sum_comm]
  have he (g : G) : ∑ i : Fin (finrank ℂ E),
      inner ℂ (stdOrthonormalBasis ℂ E i) (ρ g⁻¹ y) *
        star (inner ℂ (stdOrthonormalBasis ℂ E i) (ρ g⁻¹ x)) = inner ℂ x y := by
    simp only [← starRingEnd_apply, inner_conj_symm]
    simp_rw [mul_comm]
    rw [(stdOrthonormalBasis ℂ E).sum_inner_mul_inner, representation_inner_inverse ρ hρ,
      ← Module.End.mul_apply, ← map_mul, inv_inv, mul_inv_cancel, map_one, Module.End.one_apply]
  simp only [starRingEnd_apply, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem unitary_coefficientAction_positive (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ f).IsPositive := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro x y
    apply mul_left_cancel₀ hcard
    rw [← matrixCoefficient_basis_inner_sum ρ hρ, ← matrixCoefficient_basis_inner_sum ρ hρ]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrixCoefficient_action, matrixCoefficient_action]
    exact hf.isSymmetric _ _
  · intro x
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
      hf.re_inner_nonneg_left (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x))
    change 0 ≤ ∑ i : Fin (finrank ℂ E),
      (inner ℂ (coefficientAction finiteRegularRepresentation f
        (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x))
        (matrixCoefficient ρ (stdOrthonormalBasis ℂ E i) x)).re at h
    simp only [← matrixCoefficient_action, ← Complex.re_sum,
      matrixCoefficient_basis_inner_sum ρ hρ, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast Fintype.card_pos (α:=G))

end SignedSweeps
end

end OAI
