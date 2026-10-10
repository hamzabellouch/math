import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Inverse.ShortcodeFiberLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

/-- Exact decomposition of a uniform two-factor law with a self-loop on either
zero factor. No nonemptiness is required of the nonzero subtypes. -/
theorem uniform_pair_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Zero A] [Zero B] (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) *
        (𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0}, h p.1.val p.2.val) := by
  let R : ℝ := 𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0},
    h p.1.val p.2.val
  have : Nonempty A := ⟨0⟩
  have : Nonempty B := ⟨0⟩
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNA : (Fintype.card {a : A // a ≠ 0} : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNB : (Fintype.card {b : B // b ≠ 0} : ℝ) =
      (Fintype.card B : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : B => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNZ : (∑ a : {a : A // a ≠ 0}, ∑ b : {b : B // b ≠ 0}, h a.val b.val) =
      (Fintype.card {a : A // a ≠ 0} : ℝ) *
        (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type] using
      (Fintype.card_mul_expect
        (fun p : {a : A // a ≠ 0} × {b : B // b ≠ 0} => h p.1.val p.2.val)).symm
  have hinner (a : A) : (∑ b : B, h a b) =
      1 + ∑ b : {b : B // b ≠ 0}, h a b.val := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, hright]
  have hsum : (∑ a : A, ∑ b : B, h a b) =
      (Fintype.card B : ℝ) + (Fintype.card {a : A // a ≠ 0} : ℝ) +
        (Fintype.card {a : A // a ≠ 0} : ℝ) *
          (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a : A => ∑ b : B, h a b) 0]
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, hNZ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hfull : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) = ∑ a, ∑ b, h a b := by
    calc
      _ = (Fintype.card B : ℝ) *
          ((Fintype.card A : ℝ) * (𝔼 a, 𝔼 b, h a b)) := by ring
      _ = (Fintype.card B : ℝ) * (∑ a, 𝔼 b, h a b) := by
        rw [Fintype.card_mul_expect]
      _ = _ := by
        rw [Finset.mul_sum]
        simp_rw [Fintype.card_mul_expect]
  have hbalance : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ) + (Fintype.card B : ℝ) - 1 +
        ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    rw [hfull, hsum, hNA, hNB]
    ring
  apply mul_left_cancel₀ (mul_ne_zero hA hB)
  rw [hbalance]
  change _ = (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
    ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
      (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) * R)
  field_simp [hA, hB]
  ring

private theorem vector_card_real (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg (ell m : ℕ) :
    0 ≤ ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ := by
  have ha : 0 ≤ ((2 : ℝ) ^ ell)⁻¹ := by positivity
  have hb : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hb1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pow_add, mul_inv]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb1)]

/-- The actual equality test has a nonempty output fiber retaining at least
`η/2` after both factors are conditioned to be nonzero. The displayed order
samples a uniform matrix in that fiber first, as required by the Grassmann
neighbor correspondence. -/
theorem conditioned_output_fiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ ≤ η / 2)
    (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧
      η / 2 ≤ (matrixFiber f y).expect (fun M =>
        𝔼 p : {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0},
          if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := by
  obtain ⟨y, hy, hret⟩ := exists_output_fiber_factor_retention f haccept
  refine ⟨y, hy, ?_⟩
  have hmix := uniform_pair_mixture (fiberFactorRetention f y)
    (fiberFactorRetention_zero_left f y hy) (fiberFactorRetention_zero_right f y hy)
  simp only [vector_card_real, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg ell m) hzero (hmix ▸ hret)
  apply hconditioned.trans
  apply le_of_eq
  unfold fiberFactorRetention
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr (by ext p; simp)
  intro p _
  rfl

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
