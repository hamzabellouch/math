import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeSupport
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionCutoff

namespace OAI

/-! # The full pattern modulus and the separate giant progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The giant comparison includes internal prime squares; the external bulk
comparison keeps `bulkProgressionCutoff L`. -/
noncomputable def giantProgressionCutoff (L : ℝ) : ℕ := bulkProgressionCutoff (10 * L)

theorem giantProgressionCutoff_bounds (L : ℝ) (hL : 200 ≤ L) :
    2 ≤ giantProgressionCutoff L ∧
      Real.log (4 * (giantProgressionCutoff L : ℝ)) ≤
        2 * Real.exp ((12 / 1000 : ℝ) * L) := by
  have h := bulkProgressionCutoff_bounds (10 * L) (by linarith)
  norm_num [giantProgressionCutoff, ← mul_assoc] at h ⊢
  exact h

theorem movingArithmeticModuli_exp_bound (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ)
    (F U V : ℝ) (hr : (r : ℝ) ≤ Real.exp (F * m))
    (hP : ∀ q ∈ P, (q : ℝ) ≤ Real.exp U)
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    ((∏ b, movingArithmeticModuli r p P Finset.univ b : ℕ) : ℝ) ≤
      Real.exp (F * m + 2 * P.card * U + (m : ℝ) * V) := by
  have hprod : ((∏ q ∈ P, q : ℕ) : ℝ) ≤ Real.exp ((P.card : ℝ) * U) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _q ∈ P, Real.exp U :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hP
      _ = _ := by simp only [Finset.prod_const, ← Real.exp_nat_mul]
  have hspec : ((∏ i : Fin m, p i : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * V) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin m, Real.exp V :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hp i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  rw [movingArithmeticModuli_product]
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (F * m) * ((Real.exp ((P.card : ℝ) * U)) ^ 2 *
        Real.exp ((m : ℝ) * V)) :=
      mul_le_mul hr (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)
        hspec (Nat.cast_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The actual number of internal classes is fixed by the tree depth. Thus
internal squares fit the giant cutoff, uniformly in the pattern and its
sampled prime assignment. -/
theorem movingArithmeticModuli_giant_range (n : ℕ) (F K : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ),
      (m : ℝ) ≤ K * L → P.card ≤ 4 * n * 2 ^ n →
      (r : ℝ) ≤ Real.exp (F * m) →
      (∀ q ∈ P, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∏ b, movingArithmeticModuli r p P Finset.univ b) ≤ giantProgressionCutoff L := by
  let J : ℝ := 4 * n * 2 ^ n
  let C := F * K + 2 * J + K
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hFK : 0 ≤ F * K := mul_nonneg hF hK
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro m r p P hm hc hr hP hp
  apply Nat.le_floor
  have hbound := movingArithmeticModuli_exp_bound m r p P F
    (Real.exp ((11 / 1000 : ℝ) * L)) (Real.exp ((1 / 1000 : ℝ) * L)) hr hP hp
  apply hbound.trans
  change Real.exp _ ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * (10 * L)))
  rw [show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring]
  apply Real.exp_le_exp.mpr
  have hc' : (P.card : ℝ) ≤ J := by
    dsimp only [J]
    exact_mod_cast hc
  have he : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hKL : 0 ≤ K * L := mul_nonneg hK (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hm hF
  have hi := mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  have hiL : 2 * J * Real.exp ((11 / 1000 : ℝ) * L) ≤
      (2 * J * L) * Real.exp ((11 / 1000 : ℝ) * L) := by
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) hJ) hL) (Real.exp_nonneg _)
  have hs := mul_le_mul hm he (Real.exp_nonneg _) hKL
  have hC1 : F * K ≤ C := by dsimp only [C]; linarith
  have hC2 : 2 * J + K ≤ C := by dsimp only [C]; linarith
  have hC1L := mul_le_mul_of_nonneg_right hC1 (show 0 ≤ L by linarith)
  have hC2L := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ L by linarith)
  have hC2e := mul_le_mul_of_nonneg_right hC2L (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  nlinarith only [hmain, hi, hiL, hs, hC1L, hC2e, hrate]

end Ostmann

end OAI
