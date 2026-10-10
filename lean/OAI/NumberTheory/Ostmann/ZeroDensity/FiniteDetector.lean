import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.Ostmann.ZeroDensity.Mollifier

namespace OAI

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

namespace Ostmann.ZeroDensity

def twistedPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ArithmeticFunction ℂ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f n * χ n * (n : ℂ) ^ (-s)

theorem LSeries_eq_twistedPolynomial_of_support {q : ℕ}
    (χ : DirichletCharacter ℂ q) (f : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ)
    (hsupport : ∀ n, N < n → f n = 0) :
    LSeries (characterTwist χ f) s = twistedPolynomial χ f N s := by
  unfold LSeries twistedPolynomial
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (by simp)]
    rfl
  · intro n hn
    rw [LSeries.term_def₀ (by simp)]
    by_cases hnzero : n = 0
    · simp [hnzero]
    · have hNn : N < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      simp [hsupport n hNn]

theorem LSeries_truncate_eq_twistedPolynomial {q : ℕ}
    (χ : DirichletCharacter ℂ q) (f : ArithmeticFunction ℂ) (N : ℕ) (s : ℂ) :
    LSeries (characterTwist χ (truncate N f)) s = twistedPolynomial χ f N s := by
  rw [LSeries_eq_twistedPolynomial_of_support χ (truncate N f) N s
    (by intro n hn; simp [not_le_of_gt hn])]
  unfold twistedPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  simp [(Finset.mem_Icc.mp hn).2]

def detectorPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q) (X N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (X * N), mollifierCoefficient X N n * χ n * (n : ℂ) ^ (-s)

theorem mollifier_polynomial_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (s : ℂ) :
    twistedPolynomial χ (mollifierCoefficient X N) (X * N) s =
      1 + detectorPolynomial χ X N s := by
  classical
  have hN : 1 ≤ N := hX.trans hXN
  have hprod : 1 ≤ X * N := by
    have := Nat.mul_pos (by omega : 0 < X) (by omega : 0 < N)
    omega
  let f : ℕ → ℂ := fun n => mollifierCoefficient X N n * χ n * (n : ℂ) ^ (-s)
  have hsub : insert 1 (Finset.Ioc X (X * N)) ⊆ Finset.Icc 1 (X * N) := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hprod⟩
    · exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,
        (Finset.mem_Ioc.mp hn).2⟩
  have hsum : ∑ n ∈ insert 1 (Finset.Ioc X (X * N)), f n =
      ∑ n ∈ Finset.Icc 1 (X * N), f n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hnot1 : n ≠ 1 := by
      intro h
      subst n
      exact hnot (Finset.mem_insert_self _ _)
    have hnotIoc : n ∉ Finset.Ioc X (X * N) := fun h => hnot (Finset.mem_insert_of_mem h)
    have hnX : n ≤ X := by
      have hnmax := (Finset.mem_Icc.mp hn).2
      simp only [Finset.mem_Ioc] at hnotIoc
      omega
    have hn2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    simp [f, mollifierCoefficient_vanish hXN hn2 hnX]
  have hnot : 1 ∉ Finset.Ioc X (X * N) := by simp; omega
  rw [Finset.sum_insert hnot] at hsum
  have hf1 : f 1 = 1 := by simp [f, mollifierCoefficient_one hX hN]
  rw [hf1] at hsum
  exact hsum.symm

theorem finite_mollifier_identity {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (s : ℂ) :
    twistedPolynomial χ (μ : ArithmeticFunction ℂ) X s *
      twistedPolynomial χ (ζ : ArithmeticFunction ℂ) N s =
      1 + detectorPolynomial χ X N s := by
  rw [← LSeries_truncate_eq_twistedPolynomial,
    ← LSeries_truncate_eq_twistedPolynomial, ← mollifier_product]
  rw [LSeries_eq_twistedPolynomial_of_support χ (mollifierCoefficient X N) (X * N) s
    (fun _ hn => mollifierCoefficient_support hn)]
  exact mollifier_polynomial_split χ hX hXN s

theorem norm_moebius_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with hm | hm | hm <;> simp [hm]

theorem norm_mollifierPolynomial_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖twistedPolynomial χ (μ : ArithmeticFunction ℂ) X s‖ ≤ (X : ℝ) := by
  unfold twistedPolynomial
  calc
    ‖∑ n ∈ Finset.Icc 1 X, (μ : ArithmeticFunction ℂ) n * χ n * (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ Finset.Icc 1 X, ‖(μ : ArithmeticFunction ℂ) n * χ n * (n : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : 0 < n := by omega
      have hpower : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by simpa)
      rw [norm_mul, norm_mul]
      have hmu : ‖(μ : ArithmeticFunction ℂ) n‖ ≤ 1 := by
        simpa only [ArithmeticFunction.intCoe_apply] using norm_moebius_le_one n
      have hprod := mul_le_mul hmu (χ.norm_le_one n) (norm_nonneg _) zero_le_one
      have htotal := mul_le_mul hprod hpower (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
      simpa only [one_mul] using htotal
    _ = (X : ℝ) := by simp

theorem detector_large_of_small_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (s : ℂ)
    (hsmall : ‖twistedPolynomial χ (μ : ArithmeticFunction ℂ) X s *
      twistedPolynomial χ (ζ : ArithmeticFunction ℂ) N s‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖detectorPolynomial χ X N s‖ := by
  rw [finite_mollifier_identity χ hX hXN s] at hsmall
  have htriangle := norm_sub_le (1 + detectorPolynomial χ X N s)
    (detectorPolynomial χ X N s)
  simp only [add_sub_cancel_right, norm_one] at htriangle
  linarith

end Ostmann.ZeroDensity

end

end OAI
