import Mathlib
import OAI.Computability.DirectedFeedback.Analysis.Deletion
import OAI.Computability.DirectedFeedback.Analysis.MatrixCharacters

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixParityRow

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

end DFVSGames.Fourier.MatrixParityRow
end

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DFVSGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open DFVSGames.Integration.BinaryLinear (Vector)
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

section Additive

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H]

theorem character_average_shift (ψ : AddChar G ℂ) (A : H →+ G) (x : G) :
    (𝔼 h, ψ (x + A h)) =
      (if ψ.compAddMonoidHom A = 0 then (1 : ℂ) else 0) * ψ x := by
  classical
  have havg : (𝔼 h, (ψ.compAddMonoidHom A) h) =
      if ψ.compAddMonoidHom A = 0 then (1 : ℂ) else 0 := by
    rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
    split_ifs <;> simp
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.mul_expect]
  change ψ x * (𝔼 h, (ψ.compAddMonoidHom A) h) = _
  rw [havg, mul_comm]

end Additive

def dotCharacter {m : Nat} (w : Vector m) : AddChar (Vector m) ℂ where
  toFun ℓ := binarySign (ℓ ⬝ᵥ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [add_dotProduct, binarySign_add]

@[simp] theorem dotCharacter_apply {m : Nat} (w ℓ : Vector m) :
    dotCharacter w ℓ = binarySign (ℓ ⬝ᵥ w) := rfl

theorem dotCharacter_eq_zero_iff {m : Nat} (w : Vector m) :
    dotCharacter w = 0 ↔ w = 0 := by
  classical
  constructor
  · intro h
    funext i
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (Vector m) ℂ => ψ (Pi.single i 1)) h
    simpa [dotCharacter, single_one_dotProduct] using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_dotCharacter {m : Nat} (w : Vector m) :
    (𝔼 ℓ, binarySign (ℓ ⬝ᵥ w)) = if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, dotCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [dotCharacter_eq_zero_iff]
  split_ifs <;> simp

theorem average_rankOne_character {m n : Nat}
    (S : Matrix (Fin m) (Fin n) F2) (v : Vector n) :
    (𝔼 ℓ : Vector m, traceCharacter S (Matrix.vecMulVec v ℓ)) =
      if S *ᵥ v = 0 then (1 : ℂ) else 0 := by
  simp only [traceCharacter_apply, tracePair, MatrixParity.trace_rankOne]
  exact average_dotCharacter _

def noiseOperator {m n : Nat} (weight : Vector n → ℝ)
    (f : Matrix (Fin n) (Fin m) F2 → ℂ)
    (X : Matrix (Fin n) (Fin m) F2) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : Vector m, f (X + Matrix.vecMulVec v ℓ))

def noiseEigenvalue {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) : ℝ :=
  ∑ v, weight v * if S *ᵥ v = 0 then 1 else 0

theorem noiseOperator_character {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (X : Matrix (Fin n) (Fin m) F2) :
    noiseOperator weight (traceCharacter S) X =
      (noiseEigenvalue weight S : ℂ) * traceCharacter S X := by
  classical
  unfold noiseOperator noiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_rankOne_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S *ᵥ v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem noiseEigenvalue_nonneg {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (hw : ∀ v, 0 ≤ weight v) :
    0 ≤ noiseEigenvalue weight S := by
  unfold noiseEigenvalue
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hw]

theorem noiseEigenvalue_le_one {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (hw : ∀ v, 0 ≤ weight v)
    (hnorm : ∑ v, weight v = 1) : noiseEigenvalue weight S ≤ 1 := by
  unfold noiseEigenvalue
  calc
    (∑ v, weight v * if S *ᵥ v = 0 then 1 else 0) ≤ ∑ v, weight v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp [hw]
    _ = 1 := hnorm

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def evaluationCharacter (w : E) : AddChar (E →ₗ[F2] F2) ℂ where
  toFun ℓ := binarySign (ℓ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [LinearMap.add_apply, binarySign_add]

@[simp] theorem evaluationCharacter_apply (w : E) (ℓ : E →ₗ[F2] F2) :
    evaluationCharacter w ℓ = binarySign (ℓ w) := rfl

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

theorem average_smulRight_character [FiniteDimensional F2 F]
    [Fintype (E →ₗ[F2] F2)] (S : F →ₗ[F2] E) (v : F) :
    (𝔼 ℓ : E →ₗ[F2] F2, linearTraceCharacter S (ℓ.smulRight v)) =
      if S v = 0 then (1 : ℂ) else 0 := by
  simp only [linearTraceCharacter_apply, linearTracePair,
    MatrixParity.trace_smulRight_comp]
  exact average_evaluationCharacter _

def linearNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

theorem linearNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearNoiseOperator weight (f i) X := by
  unfold linearNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℂ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (fun Y => c * f Y) X =
      c * linearNoiseOperator weight f X := by
  unfold linearNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

def linearNoiseEigenvalue [Fintype F] (weight : F → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ v, weight v * if S v = 0 then 1 else 0

theorem linearNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (linearTraceCharacter S) X =
      (linearNoiseEigenvalue weight S : ℂ) * linearTraceCharacter S X := by
  classical
  unfold linearNoiseOperator linearNoiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_smulRight_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem linearNoiseEigenvalue_nonneg [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v) :
    0 ≤ linearNoiseEigenvalue weight S := by
  unfold linearNoiseEigenvalue
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hw]

theorem linearNoiseEigenvalue_le_one [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v)
    (hnorm : ∑ v, weight v = 1) : linearNoiseEigenvalue weight S ≤ 1 := by
  unfold linearNoiseEigenvalue
  calc
    (∑ v, weight v * if S v = 0 then 1 else 0) ≤ ∑ v, weight v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp [hw]
    _ = 1 := hnorm

def linearRealNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ v, weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

theorem linearRealNoiseOperator_complex [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    (linearRealNoiseOperator weight f X : ℂ) =
      linearNoiseOperator weight (fun Y => (f Y : ℂ)) X := by
  unfold linearRealNoiseOperator linearNoiseOperator
  change Complex.ofRealHom (∑ v, weight v * _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, complex_ofReal_expect]

theorem linearRealNoiseOperator_eq_re [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      (linearNoiseOperator weight (fun Y => (f Y : ℂ)) X).re := by
  rw [← linearRealNoiseOperator_complex]
  rfl

theorem linearRealNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearRealNoiseOperator weight (f i) X := by
  unfold linearRealNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearRealNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => c * f Y) X =
      c * linearRealNoiseOperator weight f X := by
  unfold linearRealNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

theorem linearRealNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => (linearTraceCharacter S Y).re) X =
      linearNoiseEigenvalue weight S * (linearTraceCharacter S X).re := by
  apply Complex.ofReal_injective
  rw [linearRealNoiseOperator_complex]
  simpa only [Complex.ofReal_mul, linearTraceCharacter_real] using
    (linearNoiseOperator_character weight S X)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearRealNoiseOperator_expansion (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S *
        (linearTraceCharacter S X).re := by
  classical
  calc
    linearRealNoiseOperator weight f X = linearRealNoiseOperator weight
        (fun Y => ∑ S : F →ₗ[F2] E,
          linearCoeff f S * (linearTraceCharacter S Y).re) X := by
      congr 1
      funext Y
      exact (linear_fourier_inversion f Y).symm
    _ = ∑ S : F →ₗ[F2] E,
        linearCoeff f S * linearRealNoiseOperator weight
          (fun Y => (linearTraceCharacter S Y).re) X := by
      rw [linearRealNoiseOperator_sum]
      simp_rw [linearRealNoiseOperator_smul]
    _ = _ := by
      simp_rw [linearRealNoiseOperator_character]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl

theorem linearRealNoiseOperator_pairing (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S := by
  simp_rw [linearRealNoiseOperator_expansion, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (𝔼 X, f X * (linearNoiseEigenvalue weight S * linearCoeff g S *
        (linearTraceCharacter S X).re)) =
        linearNoiseEigenvalue weight S * linearCoeff g S *
          (𝔼 X, f X * (linearTraceCharacter S X).re) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro X _
      ac_rfl
    _ = _ := by unfold linearCoeff; ring

theorem linearRealNoiseOperator_selfAdjoint (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      𝔼 X, linearRealNoiseOperator weight f X * g X := by
  calc
    _ = ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S :=
      linearRealNoiseOperator_pairing weight f g
    _ = ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff g S * linearCoeff f S := by
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = 𝔼 X, g X * linearRealNoiseOperator weight f X :=
      (linearRealNoiseOperator_pairing weight g f).symm
    _ = _ := by
      apply Finset.expect_congr rfl
      intro X _
      exact mul_comm _ _

theorem linearRealNoiseOperator_coeff (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (linearRealNoiseOperator weight f) S =
      linearNoiseEigenvalue weight S * linearCoeff f S := by
  classical
  change (𝔼 X, linearRealNoiseOperator weight f X *
    (linearTraceCharacter S X).re) = _
  calc
    (𝔼 X, linearRealNoiseOperator weight f X * (linearTraceCharacter S X).re) =
        𝔼 X, (linearTraceCharacter S X).re * linearRealNoiseOperator weight f X := by
      apply Finset.expect_congr rfl
      intro X _
      exact mul_comm _ _
    _ = ∑ T : F →ₗ[F2] E, linearNoiseEigenvalue weight T *
        linearCoeff (fun X => (linearTraceCharacter S X).re) T * linearCoeff f T :=
      linearRealNoiseOperator_pairing weight _ f
    _ = _ := by
      simp only [linearCoeff_character]
      simp [mul_ite, ite_mul]

theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

theorem linearRealNoiseOperator_nonneg (weight : F → ℝ) (hw : ∀ v, 0 ≤ weight v)
    (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ 𝔼 X, f X * linearRealNoiseOperator weight f X := by
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (linearNoiseEigenvalue_nonneg weight S hw) (sq_nonneg _)

theorem linearRealNoiseOperator_cross_le (weight : F → ℝ) (hw : ∀ v, 0 ≤ weight v)
    (f g : (E →ₗ[F2] F) → ℝ) :
    2 * (𝔼 X, f X * linearRealNoiseOperator weight g X) ≤
      (𝔼 X, f X * linearRealNoiseOperator weight f X) +
        (𝔼 X, g X * linearRealNoiseOperator weight g X) := by
  rw [linearRealNoiseOperator_pairing weight f g,
    linearRealNoiseOperator_energy weight f, linearRealNoiseOperator_energy weight g,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  calc
    2 * (linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S) =
        linearNoiseEigenvalue weight S * (2 * linearCoeff f S * linearCoeff g S) := by
      ac_rfl
    _ ≤ linearNoiseEigenvalue weight S * (linearCoeff f S ^ 2 + linearCoeff g S ^ 2) :=
      mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _)
        (linearNoiseEigenvalue_nonneg weight S hw)
    _ = _ := mul_add _ _ _

theorem linearNoiseOperator_energy_re (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * (linearNoiseOperator weight (fun Y => (f Y : ℂ)) X).re) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  simp_rw [← linearRealNoiseOperator_eq_re]
  exact linearRealNoiseOperator_energy weight f

end DFVSGames.Fourier.MatrixNoise
end

end OAI
