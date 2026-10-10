import Mathlib
import OAI.Computability.MaxCut.Games.Deletion
import OAI.Computability.MaxCut.PCP.MatrixParity
import OAI.Computability.MaxCut.Games.MatrixFourier

namespace OAI

/-! Fourier expansion of actual affine restrictions and parity extraction. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixParityRow

open MatrixCharacters MatrixFourier MatrixParity
open scoped BigOperators Classical

variable {E C V : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [AddCommGroup V] [Module F2 V]
  [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)] in
theorem traceCharacter_comp (Q : E →ₗ[F2] V) (A : V →ₗ[F2] C)
    (T : C →ₗ[F2] E) :
    linearTraceCharacter T (A.comp Q) = linearTraceCharacter (Q.comp T) A := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
theorem traceCharacter_re_add (T : C →ₗ[F2] E) (X Y : E →ₗ[F2] C) :
    (linearTraceCharacter T (X + Y)).re =
      (linearTraceCharacter T X).re * (linearTraceCharacter T Y).re := by
  rw [AddChar.map_add_eq_mul, Complex.mul_re]
  simp [linearTraceCharacter_apply, binarySign_im]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
/-- Characters restricted to the row vanish unless the dual map lands in the
kernel of `Q`. For `Q = W.mkQ` this is precisely `range T ≤ W`. -/
theorem row_character_average (Q : E →ₗ[F2] V) (T : C →ₗ[F2] E) :
    (𝔼 A : V →ₗ[F2] C, (linearTraceCharacter T (A.comp Q)).re) =
      if Q.comp T = 0 then 1 else 0 := by
  have hcomplex : (𝔼 A : V →ₗ[F2] C,
      linearTraceCharacter T (A.comp Q)) = if Q.comp T = 0 then 1 else 0 := by
    simp only [traceCharacter_comp, Fintype.expect_eq_sum_div_card,
      sum_linearTraceCharacter]
    split <;> simp [Fintype.card_ne_zero]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re] using h

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] in
/-- Averaging a finite trace-character expansion on an actual affine row. -/
theorem row_spectral_average (Q : E →ₗ[F2] V) (X₀ : E →ₗ[F2] C)
    (a : (C →ₗ[F2] E) → ℝ) :
    (𝔼 A : V →ₗ[F2] C, ∑ T : C →ₗ[F2] E,
      a T * (linearTraceCharacter T (X₀ + A.comp Q)).re) =
    ∑ T : C →ₗ[F2] E, if Q.comp T = 0 then
      a T * (linearTraceCharacter T X₀).re else 0 := by
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp only [traceCharacter_re_add, ← mul_assoc]
  rw [← Finset.mul_expect, row_character_average]
  split <;> simp

/-- Equation (5.18), with the primal row parametrized by actual quotient maps. -/
theorem row_fourier_average (Q : E →ₗ[F2] V) (X₀ : E →ₗ[F2] C)
    (g : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : V →ₗ[F2] C, g (X₀ + A.comp Q)) =
    ∑ T : C →ₗ[F2] E, if Q.comp T = 0 then
      linearCoeff g T * (linearTraceCharacter T X₀).re else 0 := by
  rw [← row_spectral_average]
  apply Finset.expect_congr rfl
  intro A _
  exact (linear_fourier_inversion g _).symm

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
theorem shift_character_average [Fintype C] (τ : E →ₗ[F2] F2)
    (T : C →ₗ[F2] E) :
    (𝔼 c : C, (linearTraceCharacter T (τ.smulRight c)).re) =
      if τ.comp T = 0 then 1 else 0 := by
  have hc := linearTrace_shift_average τ T
  rw [← Fintype.expect_eq_sum_div_card] at hc
  have hr := congrArg Complex.re hc
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re] using hr

/-- The folding average is the Fourier projection onto parity-zero frequencies. -/
theorem shift_fourier_average [Fintype C] (τ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] C) (g : (E →ₗ[F2] C) → ℝ) :
    (𝔼 c : C, g (X + τ.smulRight c)) =
    ∑ T : C →ₗ[F2] E, (if τ.comp T = 0 then linearCoeff g T else 0) *
      (linearTraceCharacter T X).re := by
  calc
    _ = 𝔼 c : C, ∑ T : C →ₗ[F2] E,
        linearCoeff g T * (linearTraceCharacter T (X + τ.smulRight c)).re := by
      apply Finset.expect_congr rfl
      intro c _
      exact (linear_fourier_inversion g _).symm
    _ = _ := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      simp only [traceCharacter_re_add, ← mul_assoc]
      rw [← Finset.mul_expect, shift_character_average]
      split <;> simp

/-- The parity-zero row subtotal equals the row average of the folded average. -/
theorem row_shift_fourier_average [Fintype C] (Q : E →ₗ[F2] V)
    (τ : E →ₗ[F2] F2) (X₀ : E →ₗ[F2] C) (g : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : V →ₗ[F2] C, 𝔼 c : C, g (X₀ + A.comp Q + τ.smulRight c)) =
    ∑ T : C →ₗ[F2] E, if Q.comp T = 0 ∧ τ.comp T = 0 then
      linearCoeff g T * (linearTraceCharacter T X₀).re else 0 := by
  simp only [shift_fourier_average]
  rw [row_spectral_average]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp_all

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
theorem signed_coefficient_le_abs (a : ℝ) (T : C →ₗ[F2] E)
    (X : E →ₗ[F2] C) : a * (linearTraceCharacter T X).re ≤ |a| := by
  rcases Integration.BinaryLinear.scalar_cases (linearTracePair X T) with h | h
  · simpa [linearTraceCharacter_apply, h] using le_abs_self a
  · simpa [linearTraceCharacter_apply, h] using neg_le_abs a

/-- Actual coefficient extraction from a dense affine row and a uniformly small
folding average. The row frequency count is an explicit finite cardinal bound;
the quotient/subspace specialization supplies it by counting maps into `W`. -/
theorem coefficient_of_dense_row [Fintype C] (Q : E →ₗ[F2] V)
    (τ : E →ₗ[F2] F2) (X₀ : E →ₗ[F2] C) (g : (E →ₗ[F2] C) → ℝ)
    (ρ : ℝ) (N : Nat) (ρ_pos : 0 < ρ) (N_pos : 0 < N)
    (row_count : (Finset.univ.filter fun T : C →ₗ[F2] E => Q.comp T = 0).card ≤ N)
    (dense : ρ < 𝔼 A : V →ₗ[F2] C, g (X₀ + A.comp Q))
    (shift_bound : ∀ X, (𝔼 c : C, g (X + τ.smulRight c)) ≤ ρ / 2) :
    ∃ T : C →ₗ[F2] E, Q.comp T = 0 ∧ τ.comp T ≠ 0 ∧
      ρ / (2 * (N : ℝ)) < |linearCoeff g T| := by
  classical
  let row : Finset (C →ₗ[F2] E) := Finset.univ.filter fun T => Q.comp T = 0
  let term (T : C →ₗ[F2] E) := linearCoeff g T * (linearTraceCharacter T X₀).re
  let β : ℝ := (ρ / 2) / (N : ℝ)
  have hN : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr N_pos
  have hβ : 0 ≤ β := le_of_lt (div_pos (div_pos ρ_pos zero_lt_two) hN)
  have hbudget : (N : ℝ) * β = ρ / 2 := by
    dsimp [β]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hN)]
  have htotal : ρ < ∑ T : C →ₗ[F2] E,
      if Q.comp T = 0 then term T else 0 := by
    rw [row_fourier_average] at dense
    convert dense using 1
    congr 1
    funext T
    split_ifs <;> rfl
  have hzero : (∑ T : C →ₗ[F2] E,
      if Q.comp T = 0 ∧ τ.comp T = 0 then term T else 0) ≤ ρ / 2 := by
    change (∑ T : C →ₗ[F2] E, if Q.comp T = 0 ∧ τ.comp T = 0 then
      linearCoeff g T * (linearTraceCharacter T X₀).re else 0) ≤ _
    rw [← row_shift_fourier_average]
    apply Finset.expect_le Finset.univ_nonempty
    intro A _
    exact shift_bound (X₀ + A.comp Q)
  have hsplit : (∑ T : C →ₗ[F2] E, if Q.comp T = 0 then term T else 0) =
      (∑ T : C →ₗ[F2] E, if Q.comp T = 0 ∧ τ.comp T = 0 then term T else 0) +
      ∑ T ∈ row, if τ.comp T = 0 then 0 else term T := by
    simp only [row, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp_all
  have hnonzero : ρ / 2 < ∑ T ∈ row, if τ.comp T = 0 then 0 else term T := by
    linarith
  by_contra hnone
  have hsmall : ∀ T ∈ row, (if τ.comp T = 0 then 0 else term T) ≤ β := by
    intro T hT
    split_ifs with hτ
    · exact hβ
    · have hQ : Q.comp T = 0 := (Finset.mem_filter.mp hT).2
      have hc : |linearCoeff g T| ≤ β := by
        by_contra hc
        apply hnone
        refine ⟨T, hQ, hτ, ?_⟩
        have hlarge : β < |linearCoeff g T| := lt_of_not_ge hc
        simpa only [β, div_div] using hlarge
      exact (signed_coefficient_le_abs (linearCoeff g T) T X₀).trans hc
  have hsum := Finset.sum_le_sum hsmall
  have hcard : (row.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast row_count
  have hcount := mul_le_mul_of_nonneg_right hcard hβ
  have hsum' : (∑ T ∈ row, if τ.comp T = 0 then 0 else term T) ≤
      (row.card : ℝ) * β := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
  linarith

/-- Dense-row extraction for a genuinely folded color map. The zero-parity
subtotal bound follows from folding, rather than being supplied as a hypothesis. -/
theorem coefficient_of_folded_dense_row [Fintype C]
    {D : Type*} [AddCommGroup D] [Module F2 D]
    (Q : E →ₗ[F2] V) (τ : E →ₗ[F2] F2) (X₀ : E →ₗ[F2] C)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (y : D) (ρ : ℝ) (N : Nat) (ρ_pos : 0 < ρ) (N_pos : 0 < N)
    (color_bound : 1 / (Fintype.card C : ℝ) ≤ ρ / 2)
    (row_count : (Finset.univ.filter fun T : C →ₗ[F2] E => Q.comp T = 0).card ≤ N)
    (dense : ρ < 𝔼 A : V →ₗ[F2] C, if F (X₀ + A.comp Q) = y then (1 : ℝ) else 0) :
    ∃ T : C →ₗ[F2] E, Q.comp T = 0 ∧ τ.comp T ≠ 0 ∧
      ρ / (2 * (N : ℝ)) < |linearCoeff (fun X => if F X = y then 1 else 0) T| := by
  apply coefficient_of_dense_row Q τ X₀ (fun X => if F X = y then 1 else 0)
    ρ N ρ_pos N_pos row_count dense
  intro X
  rw [Fintype.expect_eq_sum_div_card]
  exact (folded_indicator_average_le τ inclusion inclusion_injective F folded X y).trans
    color_bound

lemma color_card_bound [Fintype C] (r s : Nat) (ρ : ℝ)
    (hρ : ρ = 2 / (2 : ℝ) ^ (s - r))
    (hdim : s - r ≤ Module.finrank F2 C) :
    1 / (Fintype.card C : ℝ) ≤ ρ / 2 := by
  have hcard : Fintype.card C = 2 ^ Module.finrank F2 C := by
    simpa [F2, ZMod.card] using Module.card_fintype (Module.finBasis F2 C)
  have hleNat : 2 ^ (s - r) ≤ Fintype.card C := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hdim
  have hle : (2 : ℝ) ^ (s - r) ≤ (Fintype.card C : ℝ) := by
    exact_mod_cast hleNat
  calc
    1 / (Fintype.card C : ℝ) ≤ 1 / (2 : ℝ) ^ (s - r) :=
      one_div_le_one_div_of_le (pow_pos zero_lt_two _) hle
    _ = ρ / 2 := by rw [hρ]; ring

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
lemma fixed_row_folded {R D : Type*}
    [AddCommGroup R] [Module F2 R] [AddCommGroup D] [Module F2 D]
    (τ : E →ₗ[F2] F2) (questionInclusion : C →ₗ[F2] R)
    (colorInclusion : C →ₗ[F2] D)
    (FU : (E →ₗ[F2] R) → D) (Z : E →ₗ[F2] R)
    (folded : ∀ Y c, FU (Y + τ.smulRight (questionInclusion c)) = FU Y + colorInclusion c) :
    ∀ X c, FU (Z + questionInclusion.comp (X + τ.smulRight c)) =
      FU (Z + questionInclusion.comp X) + colorInclusion c := by
  intro X c
  have hshift : questionInclusion.comp (τ.smulRight c) = τ.smulRight (questionInclusion c) := by
    ext e
    simp [LinearMap.smulRight_apply]
  rw [LinearMap.comp_add, hshift, ← add_assoc, folded]

/-- Lemma 5.3 on an actual quotient-parametrized dense row. The density parameter
is stated as a ratio of natural powers, avoiding truncated negative exponents. -/
theorem lemma53_quotient [Fintype C]
    {D : Type*} [AddCommGroup D] [Module F2 D]
    (W : Submodule F2 E)
    [Fintype ((E ⧸ W) →ₗ[F2] C)] [Fintype (C →ₗ[F2] W)]
    (τ : E →ₗ[F2] F2) (X₀ : E →ₗ[F2] C)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (y : D) (r s : Nat) (ρ : ℝ)
    (hρ : ρ = 2 / (2 : ℝ) ^ (s - r))
    (hW : Module.finrank F2 W ≤ r)
    (hC : Module.finrank F2 C ≤ s)
    (hdim : s - r ≤ Module.finrank F2 C)
    (dense : ρ < 𝔼 A : (E ⧸ W) →ₗ[F2] C,
      if F (X₀ + A.comp W.mkQ) = y then (1 : ℝ) else 0) :
    ∃ T : C →ₗ[F2] E, τ.comp T ≠ 0 ∧
      ρ / (2 * ((2 ^ (r * s) : Nat) : ℝ)) <
        |linearCoeff (fun X => if F X = y then 1 else 0) T| := by
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact div_pos zero_lt_two (pow_pos zero_lt_two _)
  have hcount : (Finset.univ.filter fun T : C →ₗ[F2] E => W.mkQ.comp T = 0).card ≤
      2 ^ (r * s) := by
    have hcard := MatrixRestrictions.quotientKernel_filter_card (C := C) W
    have heq : (Finset.univ.filter fun T : C →ₗ[F2] E => W.mkQ.comp T = 0).card =
        Fintype.card (C →ₗ[F2] W) := by
      convert hcard using 1
      congr 1
      ext T
      simp
    rw [heq]
    exact MatrixParity.card_linearMaps_le (E := W) (C := C) r s hW hC
  obtain ⟨T, _, hτ, hβ⟩ := coefficient_of_folded_dense_row W.mkQ τ X₀
    inclusion inclusion_injective F folded y ρ (2 ^ (r * s)) hρpos
    (Nat.two_pow_pos _) (color_card_bound r s ρ hρ hdim) hcount dense
  exact ⟨T, hτ, hβ⟩

end MaxCutGames.Fourier.MatrixParityRow
end

end OAI
