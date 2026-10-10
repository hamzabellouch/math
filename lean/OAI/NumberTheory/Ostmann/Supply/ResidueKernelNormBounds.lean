import OAI.NumberTheory.Ostmann.Supply.ResidueProjectionSides
import OAI.NumberTheory.Ostmann.Supply.ResidueVectorNorm

namespace OAI

/-! # Dimension-free norms of the concrete residue kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniformResidueVector_energy {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) :
    (∑ x, ‖uniformResidueVector S x‖ ^ 2) = (S.card : ℝ)⁻¹ := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have he (x : ZMod p) : ‖uniformResidueVector S x‖ ^ 2 =
      if x ∈ S then ((S.card : ℝ)⁻¹) ^ 2 else 0 := by
    by_cases hx : x ∈ S <;> simp [uniformResidueVector, hx]
  simp_rw [he]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem uniformResidueVector_norm_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hcard : (p : ℝ) / 3 ≤ S.card) :
    residueVectorNorm (uniformResidueVector S) ≤ 2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (residueVectorNorm_le_iff _ _ (by positivity)).mpr
  rw [uniformResidueVector_energy S hS, div_pow, Real.sq_sqrt hp.le]
  norm_num
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hs hp).mpr
  linarith

theorem residueVectorNorm_cross_projection_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (centeredSupportProjection T f))) ≤
      (1 / 2 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_le_iff _ _ (by positivity [residueVectorNorm_nonneg f])).mpr
  rw [mul_pow, residueVectorNorm_sq]
  convert centeredSupportProjection_spectral_energy S T E hST f using 1
  norm_num

theorem residueVectorNorm_cross_kernel_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (t : ℝ) (ht : 0 ≤ t)
    (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (rawAdditiveKernelAction (sparseAdditiveKernel E t) (centeredSupportProjection T f))) ≤
      (t / 2) * residueVectorNorm f := by
  have he : rawAdditiveKernelAction (sparseAdditiveKernel E t) (centeredSupportProjection T f) =
      fun x => (t : ℂ) * finiteSpectralProjection E (centeredSupportProjection T f) x := by
    funext x
    exact sparseAdditiveKernel_action E t _ x
  rw [he, centeredSupportProjection_const_mul, residueVectorNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hh := mul_le_mul_of_nonneg_left (residueVectorNorm_cross_projection_le S T E hST f) ht
  convert hh using 1
  ring

theorem residueVectorNorm_square_kernel_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (t ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (f : ZMod p → ℂ) :
    residueVectorNorm (centeredSupportProjection S
      (rawAdditiveKernelAction (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x)
        (centeredSupportProjection T f))) ≤ (t ^ 2 * ε) * residueVectorNorm f := by
  apply (residueVectorNorm_centered_le _ _).trans
  apply (residueVectorNorm_raw_le _ _ _ (mul_nonneg (sq_nonneg _) hε)
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)).trans
  exact mul_le_mul_of_nonneg_left (residueVectorNorm_centered_le T f) (mul_nonneg (sq_nonneg _) hε)

end Ostmann

end OAI
