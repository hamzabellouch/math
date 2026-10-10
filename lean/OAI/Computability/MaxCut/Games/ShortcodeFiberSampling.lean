import Mathlib
import OAI.Computability.MaxCut.Games.MatrixChartShortcode

namespace OAI

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MaxCutGames.Foundations.Information

theorem matrixKernel_average {ell m : ℕ} (M : Mat ell m) (g : Mat ell m → ℝ) :
    (∑ N, matrixKernel M N * g N) = 𝔼 a, 𝔼 l, g (M + rankOne a l) := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp [ite_mul]

theorem fiberMass_eq_card {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberMass matrixWeight f y =
      ((matrixFiber f y).card : ℝ) / Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberMass
  calc
    _ = ∑ M ∈ matrixFiber f y, matrixWeight M := by
      rw [matrixFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _
      by_cases h : f M = y <;> simp [h]
    _ = _ := by simp [matrixWeight, div_eq_mul_inv]

theorem fiberMass_pos_iff {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    0 < EqualityFiber.fiberMass matrixWeight f y ↔ (matrixFiber f y).Nonempty := by
  rw [fiberMass_eq_card]
  have hcard : (0 : ℝ) < Fintype.card (Mat ell m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]

def fiberFactorRetention {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) (a : Vector ell) (l : Vector m) : ℝ :=
  (matrixFiber f y).expect fun M => if f (M + rankOne a l) = y then 1 else 0

theorem fiberFlow_eq {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y =
      (∑ M ∈ matrixFiber f y,
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) /
        Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberFlow
  simp_rw [matrixKernel_average]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [matrixFiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : f M = y
  · simp [h, matrixWeight, mul_comm]
  · simp [h]

theorem fiber_retention_eq_factor_average {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
      EqualityFiber.fiberMass matrixWeight f y =
        𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  rw [fiberFlow_eq, fiberMass_eq_card]
  have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : (𝔼 a, 𝔼 l, fiberFactorRetention f y a l) =
      (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
    unfold fiberFactorRetention
    calc
      _ = 𝔼 a, (matrixFiber f y).expect (fun M =>
          𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
      _ = _ := Finset.expect_comm _ _ _
  rw [hswap, Finset.expect_eq_sum_div_card]
  simp [div_div_div_cancel_right₀ hcard]

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

/-- A nonempty actual output fiber whose retention under the full factor law
is at least the original equality acceptance threshold. -/
theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := Shortcode.exists_output_fiber f haccept
  exact ⟨y, (fiberMass_pos_iff f y).mp hy,
    by simpa only [fiber_retention_eq_factor_average] using hret⟩

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

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

private theorem vector_card_real_inline_ShortcodeFiberConditioning (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning (ell m : ℕ) :
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
  simp only [vector_card_real_inline_ShortcodeFiberConditioning, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning ell m) hzero (hmix ▸ hret)
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
end MaxCutGames.Inverse.ShortcodeFromGrassmann

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- The finite sampling bridge has no expansion or inverse premise. -/
theorem chartFiberRetention : ChartFiberRetention := by
  intro ell m _hell _hm η hη hη1 hzero f haccept
  obtain ⟨y, hnonempty, hretention⟩ :=
    conditioned_output_fiber f hη hη1 hzero haccept
  refine ⟨y, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hnonempty
  · rw [liftedFiber_retention_eq_half]
    have h : η / 2 ≤ (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := hretention
    linarith

/-- Conditional Grassmann-to-matrix implication, preserving all quantifiers
and the affine target. KMS expansion is the sole remaining displayed premise.
-/
theorem inversePrinciple_of_expansion (hKMS : KMS.ExpansionPrinciple) :
    Shortcode.InversePrinciple :=
  inversePrinciple_of_expansion_and_chart hKMS chartFiberRetention

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! The unconditional affine matrix inverse theorem. The Grassmann theorem,
chart retention, zero-factor correction, output-fiber extraction, and affine
row/column slice construction are all proved in its dependency chain. -/

namespace MaxCutGames.Inverse.ShortcodeTheorem
noncomputable section

/-- Full-factor sampling includes zero. The conclusion retains an affine
intercept and applies to arbitrary matrix labelings without a folding premise. -/
theorem inversePrinciple : Shortcode.InversePrinciple :=
  ShortcodeFromGrassmann.inversePrinciple_of_expansion KMSExpansion.kms_expansion

end
end MaxCutGames.Inverse.ShortcodeTheorem

end OAI
