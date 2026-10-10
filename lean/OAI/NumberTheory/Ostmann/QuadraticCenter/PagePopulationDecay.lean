import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.QuadraticCenter.PageKernelPopulation

namespace OAI

/-!
# Decay of the exceptional Page-kernel population

At the manuscript's threshold `R = (log X)^100`, the already proved
population bound is smaller than `X / (log X)^40`, uniformly in the
small common-center denominator. No analytic estimate is added here.
-/

namespace Ostmann

open Filter Asymptotics

/-- One cutoff absorbs both square-root population errors uniformly for all
denominators bounded by `exp(η L)`, with `η ≤ 1/1000`. -/
theorem exists_page_population_error_cutoff :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L η : ℝ, L₀ ≤ L → η ≤ 1 / 1000 →
      ∀ m : ℕ, (m : ℝ) ≤ Real.exp (η * L) →
        Real.exp L / Real.sqrt (L ^ (100 : ℕ)) +
            2 * Real.sqrt (Real.exp L * m) + m ≤
          4 * (Real.exp L / L ^ (40 : ℕ)) := by
  have hpoly := (isLittleO_pow_exp_pos_mul_atTop 40
    (by norm_num : (0 : ℝ) < 1 / 4)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hpoly
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro L η hL hη m hm
  have hL1 : 1 ≤ L := (le_max_left 1 M).trans hL
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hM' := hM L ((le_max_right 1 M).trans hL)
  have hpower : L ^ (40 : ℕ) ≤ Real.exp ((1 / 4 : ℝ) * L) := by
    apply (le_abs_self (L ^ (40 : ℕ))).trans
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] using hM'
  have hmain : Real.exp ((3 / 4 : ℝ) * L) ≤ Real.exp L / L ^ (40 : ℕ) := by
    apply (le_div_iff₀ (pow_pos hLp 40)).mpr
    have h := mul_le_mul_of_nonneg_left hpower
      (Real.exp_pos ((3 / 4 : ℝ) * L)).le
    rw [← Real.exp_add] at h
    have hsum : (3 / 4 : ℝ) * L + (1 / 4 : ℝ) * L = L := by ring
    rwa [hsum] at h
  have hmhalf : (m : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * L) := by
    apply hm.trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmthree : (m : ℝ) ≤ Real.exp ((3 / 4 : ℝ) * L) := by
    apply hm.trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsqrt : Real.sqrt (Real.exp L * m) ≤ Real.exp ((3 / 4 : ℝ) * L) := by
    have hmul := mul_le_mul_of_nonneg_left hmhalf (Real.exp_pos L).le
    have h := Real.sqrt_le_sqrt hmul
    have heq : Real.exp L * Real.exp ((1 / 2 : ℝ) * L) =
        (Real.exp ((3 / 4 : ℝ) * L)) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq, Real.sqrt_sq (Real.exp_pos _).le] at h
    exact h
  have hsqrt100 : Real.sqrt (L ^ (100 : ℕ)) = L ^ (50 : ℕ) := by
    rw [show L ^ (100 : ℕ) = (L ^ (50 : ℕ)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hleading : Real.exp L / Real.sqrt (L ^ (100 : ℕ)) ≤
      Real.exp L / L ^ (40 : ℕ) := by
    rw [hsqrt100]
    exact div_le_div_of_nonneg_left (Real.exp_pos L).le (pow_pos hLp 40)
      (pow_le_pow_right₀ hL1 (by omega : 40 ≤ 50))
  have hsqrt' := hsqrt.trans hmain
  have hm' := hmthree.trans hmain
  linarith

/-- The actual exceptional pair family at `R = L^100` has negligible
population on the endpoint-product scale `exp L / L^6`. The exponent forty
retains a fixed reserve for the subsequent common-center selections. -/
theorem exists_page_population_decay :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧
      ∀ (P : PublishedProgressionInput) (Q₀ : ℕ) (L η : ℝ),
      L₀ ≤ L → η ≤ 1 / 1000 →
      ∀ (S T : Finset ℤ) (f g : ℤ → ℤ) (r s : ℤ → ℕ) (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z =>
        f z.1 * g z.2 ∈ pageKernelExclusion P Q₀ (L ^ (100 : ℕ))).card : ℝ) ≤
        C * (Real.exp L / L ^ (40 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_page_kernel_population_bound
  obtain ⟨L₀, hL₀, hcut⟩ := exists_page_population_error_cutoff
  refine ⟨4 * C, L₀, by positivity, hL₀, ?_⟩
  intro P Q₀ L η hL hη S T f g r s m h hm hmupper hf hg hred hr hs hspanS hspanT hcross
  have hLp : 0 < L := lt_of_lt_of_le (by linarith : (0 : ℝ) < L₀) hL
  have hb := hbound P Q₀ (L ^ (100 : ℕ)) S T f g r s m h (Real.exp L)
    (pow_pos hLp 100) hm (Real.exp_pos L).le hf hg hred hr hs hspanS hspanT hcross
  calc
    _ ≤ C * (Real.exp L / Real.sqrt (L ^ (100 : ℕ)) +
        2 * Real.sqrt (Real.exp L * m) + m) := hb
    _ ≤ C * (4 * (Real.exp L / L ^ (40 : ℕ))) :=
      mul_le_mul_of_nonneg_left (hcut L η hL hη m hmupper) hC.le
    _ = _ := by ring

end Ostmann

end OAI
