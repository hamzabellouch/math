import OAI.NumberTheory.Ostmann.Arithmetic.BulkSymmetrization
import OAI.NumberTheory.Ostmann.Tree.BadArrangementFraction

namespace OAI

/-! # Pair-correlation control of the symmetrized amplitude -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteFamilyAverage {J X : Type*} [Fintype J]
    (A : J → X → ℂ) (x : X) : ℂ :=
  (Fintype.card J : ℂ)⁻¹ * ∑ j, A j x

theorem finiteFamilyAverage_norm_sq {J X : Type*} [Fintype J]
    (A : J → X → ℂ) (x : X) :
    ‖finiteFamilyAverage A x‖ ^ 2 =
      ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        (∑ i : J, ∑ j : J, A i x * star (A j x)).re := by
  have hs : (∑ i : J, ∑ j : J, A i x * star (A j x)) =
      (∑ i, A i x) * star (∑ j, A j x) := by
    rw [star_sum, Finset.sum_mul_sum]
  rw [hs, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  unfold finiteFamilyAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]

theorem finiteFamilyAverage_energy_le {J X : Type*} [Fintype J] [Fintype X]
    (μ : X → ℝ) (A : J → X → ℂ) :
    (∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2) ≤
      ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ i : J, ∑ j : J, ‖∑ x, (μ x : ℂ) * (A i x * star (A j x))‖ := by
  simp_rw [finiteFamilyAverage_norm_sq A]
  have hs :
      (∑ x, μ x * (∑ i : J, ∑ j : J, A i x * star (A j x)).re) =
        ∑ i : J, ∑ j : J, (∑ x, (μ x : ℂ) * (A i x * star (A j x))).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _ = ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ x, μ x * (∑ i : J, ∑ j : J, A i x * star (A j x)).re := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := congrArg (fun z => ((Fintype.card J : ℝ)⁻¹) ^ 2 * z) hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Complex.re_le_norm _)
      (sq_nonneg _)

theorem sum_relative_function {J : Type*} [Group J] [Fintype J]
    (f : J → ℝ) (i : J) : (∑ j, f (i⁻¹ * j)) = ∑ j, f j :=
  (Equiv.mulLeft i⁻¹).bijective.sum_comp f

/-- Bad pairs are counted by a single relative permutation. No invariance
of individual amplitudes or support conditions is required. -/
theorem finiteFamilyAverage_good_bad_bound {J X : Type*} [Group J] [Fintype J]
    [Fintype X] (μ : X → ℝ) (A : J → X → ℂ)
    (bad : J → Prop) (B E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i j, ‖∑ x, (μ x : ℂ) * (A i x * star (A j x))‖ ≤
      if bad (i⁻¹ * j) then B else E) :
    (∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2) ≤
      (Fintype.card {j : J // bad j} : ℝ) / Fintype.card J * B + E := by
  have hc : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc0 : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ j : J, if bad j then B else E) ≤
      (Fintype.card {j : J // bad j} : ℝ) * B + (Fintype.card J : ℝ) * E := by
    calc
      _ ≤ ∑ j : J, ((if bad j then B else 0) + E) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> linarith
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, Fintype.card_subtype]
  apply (finiteFamilyAverage_energy_le μ A).trans
  calc
    _ ≤ ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ i : J, ∑ j : J, if bad (i⁻¹ * j) then B else E := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ((Fintype.card J : ℝ) * ∑ j : J, if bad j then B else E) := by
      simp only [sum_relative_function (fun j => if bad j then B else E),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ((Fintype.card J : ℝ) *
          ((Fintype.card {j : J // bad j} : ℝ) * B + (Fintype.card J : ℝ) * E)) := by
      gcongr
    _ = _ := by field_simp

end Ostmann

end OAI
